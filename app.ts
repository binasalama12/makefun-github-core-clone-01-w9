// sage-owl-51: a GitHub-compatible git forge built around an ACTOR-PER-REPO design.
//
// Architecture: every repository is an actor. An actor owns its repository record and a mailbox —
// a promise chain that works as a FIFO queue. Every operation that touches a repository (a REST
// write, a contents commit, a merge, a git push, an MCP tool call, a GraphQL mutation) is posted
// to that repository's mailbox and runs only when the messages ahead of it have finished, so a
// repository never sees two interleaved mutations and per-repo consistency needs no locks. The
// supervisor (Forge class) owns the actor registry, hands out repository actors by "owner/name",
// and owns the shared git object pool: blobs, trees and commits are content-addressed and immutable,
// so all actors may safely read them outside their mailbox, while ref tips live inside the actor.
// Surfaces: REST v3 under /api/v3, GraphQL at /api/graphql, MCP at /mcp, git smart HTTP at
// /{owner}/{repo}.git — all four are thin translators that post messages to the same actors.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash, randomUUID } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// --------------------------------------------------------------------------- constants

const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const OWNER = 'adaiversen';
const OWNER_ID = 1000;
const OWNER_NAME = 'Ada Iversen';
const OWNER_EMAIL = 'adaiversen@example.invalid';
const ZERO_OID = '0000000000000000000000000000000000000000';
const EPOCH = 1735689600; // 2025-01-01T00:00:00Z: every timestamp derives from this plus a counter.
const JSON_TYPE = 'application/json; charset=utf-8';
const VERSION = '1.0.0';

let requestSeq = 0;
let commitSeq = 0;
let commentSeq = 0;
let labelSeq = 0;

function isoAt(seq: number): string {
  return new Date((EPOCH + seq) * 1000).toISOString();
}

// --------------------------------------------------------------------------- pkt-lines

function pkt(payload: string | Buffer): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const head = (body.length + 4).toString(16).padStart(4, '0');
  return Buffer.concat([Buffer.from(head, 'ascii'), body]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

/** Decode every pkt-line in a request body; throws on malformed framing. */
function decodePkts(body: Buffer): Array<{ kind: string; payload: Buffer }> {
  const out: Array<{ kind: string; payload: Buffer }> = [];
  let pos = 0;
  while (pos < body.length) {
    if (pos + 4 > body.length) throw new Error('truncated pkt-line');
    const head = body.subarray(pos, pos + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) throw new Error('bad pkt-line header');
    const len = parseInt(head, 16);
    if (len === 0) { out.push({ kind: 'flush', payload: Buffer.alloc(0) }); pos += 4; continue; }
    if (len === 1) { out.push({ kind: 'delim', payload: Buffer.alloc(0) }); pos += 4; continue; }
    if (len === 2) { out.push({ kind: 'response-end', payload: Buffer.alloc(0) }); pos += 4; continue; }
    if (len < 4 || pos + len > body.length) throw new Error('bad pkt-line length');
    out.push({ kind: 'data', payload: body.subarray(pos + 4, pos + len) });
    pos += len;
  }
  return out;
}

// --------------------------------------------------------------------------- git object pool (shared, supervised)

type ObjType = 'blob' | 'tree' | 'commit' | 'tag';
const TYPE_CODES: Record<string, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPES: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

interface GitObj { type: ObjType; data: Buffer }

const objectPool = new Map<string, GitObj>();

function hashObject(type: ObjType, data: Buffer): string {
  const hash = createHash('sha1');
  hash.update(Buffer.from(`${type} ${data.length}\0`, 'utf8'));
  hash.update(data);
  return hash.digest('hex');
}

function storeObject(type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!objectPool.has(oid)) objectPool.set(oid, { type, data });
  return oid;
}

function getObject(oid: string): GitObj | undefined {
  return objectPool.get(oid);
}

// --------------------------------------------------------------------------- packfiles

function packObjectHeader(type: ObjType, size: number): Buffer {
  const code = TYPE_CODES[type] ?? 3;
  const bytes: number[] = [];
  let first = (code << 4) | (size & 0x0f);
  size = Math.floor(size / 16);
  if (size > 0) first |= 0x80;
  bytes.push(first);
  while (size > 0) {
    let b = size & 0x7f;
    size = Math.floor(size / 128);
    if (size > 0) b |= 0x80;
    bytes.push(b);
  }
  return Buffer.from(bytes);
}

/** A whole-object pack (no deltas): simple, and every object recomputes to its id. */
function writePack(oids: string[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(oids.length, 8);
  parts.push(header);
  for (const oid of oids) {
    const obj = objectPool.get(oid);
    if (!obj) continue;
    parts.push(packObjectHeader(obj.type, obj.data.length));
    parts.push(deflateSync(obj.data));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

/** Inflate one zlib stream starting at `pos`; returns the data and the offset just past the stream. */
function inflateAt(buf: Buffer, pos: number, expectedSize: number): { data: Buffer; next: number } {
  // The smallest prefix that inflates to the full object is exactly the stream: shorter prefixes
  // are truncated and refuse, longer ones carry the next object and would corrupt the walk.
  // A deflate stream is never much larger than its output, so search a window sized by the object
  // first; if that fails (a pathological stream), fall back to the whole remaining buffer.
  const remaining = buf.length - pos;
  const window = Math.min(remaining, expectedSize + Math.ceil(expectedSize / 8) + 512);
  const search = (limit: number): { data: Buffer; next: number } | null => {
    let lo = 1;
    let hi = limit;
    let best: { data: Buffer; next: number } | null = null;
    while (lo <= hi) {
      const mid = Math.floor((lo + hi) / 2);
      try {
        const data = inflateSync(buf.subarray(pos, pos + mid));
        if (data.length === expectedSize) { best = { data, next: pos + mid }; hi = mid - 1; }
        else if (data.length < expectedSize) lo = mid + 1;
        else hi = mid - 1;
      } catch {
        lo = mid + 1;
      }
    }
    return best;
  };
  const found = search(window) ?? (window < remaining ? search(remaining) : null);
  if (!found) throw new Error('corrupt pack object stream');
  return found;
}

/** Apply a git delta buffer to a base object. */
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let pos = 0;
  const readVarint = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const b = delta[pos] ?? 0;
      pos += 1;
      value += (b & 0x7f) * 2 ** shift;
      shift += 7;
      if ((b & 0x80) === 0) break;
    }
    return value;
  };
  readVarint(); // source size
  const targetSize = readVarint();
  const chunks: Buffer[] = [];
  while (pos < delta.length) {
    const op = delta[pos] ?? 0;
    pos += 1;
    if (op & 0x80) {
      let offset = 0;
      let size = 0;
      for (let i = 0; i < 4; i += 1) { if (op & (1 << i)) { offset += (delta[pos] ?? 0) * 2 ** (8 * i); pos += 1; } }
      for (let i = 0; i < 3; i += 1) { if (op & (0x10 << i)) { size += (delta[pos] ?? 0) * 2 ** (8 * (i + 2)); pos += 1; } }
      if (size === 0) size = 0x10000;
      chunks.push(base.subarray(offset, offset + size));
    } else if (op > 0) {
      chunks.push(delta.subarray(pos, pos + op));
      pos += op;
    } else {
      throw new Error('bad delta opcode');
    }
  }
  const out = Buffer.concat(chunks);
  if (out.length !== targetSize) throw new Error('delta size mismatch');
  return out;
}

interface PackEntry { oid: string; type: ObjType; data: Buffer }

/** Read a pack into the shared pool, resolving OFS/REF deltas against the pack or the pool. */
function readPack(pack: Buffer): PackEntry[] {
  if (pack.length < 12 + 20 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('not a pack');
  const count = pack.readUInt32BE(8);
  let pos = 12;
  const entries: PackEntry[] = [];
  const byOffset = new Map<number, PackEntry>();
  for (let i = 0; i < count; i += 1) {
    const start = pos;
    let byte = pack[pos] ?? 0;
    pos += 1;
    const typeCode = (byte >> 4) & 0x07;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = pack[pos] ?? 0;
      pos += 1;
      size += (byte & 0x7f) * 2 ** shift;
      shift += 7;
    }
    if (typeCode === 6) { // OFS_DELTA
      let b = pack[pos] ?? 0;
      pos += 1;
      let offset = b & 0x7f;
      while (b & 0x80) {
        b = pack[pos] ?? 0;
        pos += 1;
        offset = ((offset + 1) << 7) + (b & 0x7f);
      }
      const baseEntry = byOffset.get(start - offset);
      if (!baseEntry) throw new Error('ofs-delta base missing');
      const { data, next } = inflateAt(pack, pos, size);
      pos = next;
      const full = applyDelta(baseEntry.data, data);
      const entry: PackEntry = { oid: hashObject(baseEntry.type, full), type: baseEntry.type, data: full };
      entries.push(entry); byOffset.set(start, entry);
    } else if (typeCode === 7) { // REF_DELTA
      const baseOid = pack.subarray(pos, pos + 20).toString('hex');
      pos += 20;
      const baseObj = objectPool.get(baseOid) ?? entries.find((e) => e.oid === baseOid);
      if (!baseObj) throw new Error('ref-delta base missing');
      const { data, next } = inflateAt(pack, pos, size);
      pos = next;
      const full = applyDelta(baseObj.data, data);
      const entry: PackEntry = { oid: hashObject(baseObj.type, full), type: baseObj.type, data: full };
      entries.push(entry); byOffset.set(start, entry);
    } else {
      const type = CODE_TYPES[typeCode];
      if (!type) throw new Error(`unknown pack type ${typeCode}`);
      const { data, next } = inflateAt(pack, pos, size);
      pos = next;
      const entry: PackEntry = { oid: hashObject(type, data), type, data };
      entries.push(entry); byOffset.set(start, entry);
    }
  }
  for (const entry of entries) {
    if (!objectPool.has(entry.oid)) objectPool.set(entry.oid, { type: entry.type, data: entry.data });
  }
  return entries;
}

// --------------------------------------------------------------------------- object graph helpers

interface CommitInfo { tree: string; parents: string[]; message: string; authorLine: string }

function parseCommit(data: Buffer): CommitInfo {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split >= 0 ? text.slice(0, split) : text;
  const message = split >= 0 ? text.slice(split + 2) : '';
  let tree = ZERO_OID;
  let authorLine = '';
  const parents: string[] = [];
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) authorLine = line.slice(7);
  }
  return { tree, parents, message, authorLine };
}

function parseTree(data: Buffer): Array<{ mode: string; name: string; oid: string }> {
  const entries: Array<{ mode: string; name: string; oid: string }> = [];
  let pos = 0;
  while (pos < data.length) {
    const space = data.indexOf(0x20, pos);
    const mode = data.subarray(pos, space).toString('ascii');
    const nul = data.indexOf(0x00, space);
    const name = data.subarray(space + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    pos = nul + 21;
  }
  return entries;
}

interface FileEntry { sha: string; mode: string }

/** Flatten a commit's tree into path -> blob, plus directory -> tree sha. */
function filesAt(commitOid: string): { files: Map<string, FileEntry>; dirs: Map<string, string> } {
  const files = new Map<string, FileEntry>();
  const dirs = new Map<string, string>();
  const commit = getObject(commitOid);
  if (!commit || commit.type !== 'commit') return { files, dirs };
  const walk = (treeOid: string, prefix: string): void => {
    const tree = getObject(treeOid);
    if (!tree || tree.type !== 'tree') return;
    for (const entry of parseTree(tree.data)) {
      const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
      if (entry.mode === '40000') {
        dirs.set(path, entry.oid);
        walk(entry.oid, path);
      } else {
        files.set(path, { sha: entry.oid, mode: entry.mode });
      }
    }
  };
  walk(parseCommit(commit.data).tree, '');
  return { files, dirs };
}

/** Build (and store) nested trees for a flat path -> blob map; returns the root tree id. */
function buildTree(files: Map<string, FileEntry>): string {
  interface Node { files: Map<string, FileEntry>; dirs: Map<string, Node> }
  const root: Node = { files: new Map(), dirs: new Map() };
  for (const [path, entry] of files) {
    const segments = path.split('/');
    let node = root;
    for (let i = 0; i < segments.length - 1; i += 1) {
      const name = segments[i] as string;
      if (!node.dirs.has(name)) node.dirs.set(name, { files: new Map(), dirs: new Map() });
      node = node.dirs.get(name) as Node;
    }
    node.files.set(segments[segments.length - 1] as string, entry);
  }
  const emit = (node: Node): string => {
    const items: Array<{ mode: string; name: string; oid: string; dir: boolean }> = [];
    for (const [name, entry] of node.files) items.push({ mode: entry.mode, name, oid: entry.sha, dir: false });
    for (const [name, child] of node.dirs) items.push({ mode: '40000', name, oid: emit(child), dir: true });
    items.sort((a, b) => {
      const ka = a.dir ? `${a.name}/` : a.name;
      const kb = b.dir ? `${b.name}/` : b.name;
      return ka < kb ? -1 : ka > kb ? 1 : 0;
    });
    const chunks: Buffer[] = [];
    for (const item of items) {
      chunks.push(Buffer.from(`${item.mode} ${item.name}\0`, 'utf8'));
      chunks.push(Buffer.from(item.oid, 'hex'));
    }
    return storeObject('tree', Buffer.concat(chunks));
  };
  return emit(root);
}

/** All commit ancestors of `tip` (including itself), nearest first. */
function ancestorsOf(tip: string): string[] {
  const seen = new Set<string>();
  const order: string[] = [];
  const queue: string[] = [tip];
  while (queue.length > 0) {
    const oid = queue.shift() as string;
    if (seen.has(oid)) continue;
    const obj = getObject(oid);
    if (!obj || obj.type !== 'commit') continue;
    seen.add(oid);
    order.push(oid);
    for (const parent of parseCommit(obj.data).parents) queue.push(parent);
  }
  return order;
}

function isAncestor(maybeAncestor: string, tip: string): boolean {
  return ancestorsOf(tip).includes(maybeAncestor);
}

function mergeBase(a: string, b: string): string | null {
  const ancestorsA = new Set(ancestorsOf(a));
  for (const candidate of ancestorsOf(b)) {
    if (ancestorsA.has(candidate)) return candidate;
  }
  return null;
}

/** Every object reachable from a commit/tag: commits, their trees and blobs, tag objects. */
function reachableObjects(tips: string[], maxGeneration: number | null): Set<string> {
  const out = new Set<string>();
  const addTree = (treeOid: string): void => {
    if (out.has(treeOid)) return;
    const tree = getObject(treeOid);
    if (!tree || tree.type !== 'tree') return;
    out.add(treeOid);
    for (const entry of parseTree(tree.data)) {
      if (entry.mode === '40000') addTree(entry.oid);
      else out.add(entry.oid);
    }
  };
  const queue: Array<{ oid: string; gen: number }> = tips.map((oid) => ({ oid, gen: 1 }));
  const seenCommit = new Set<string>();
  while (queue.length > 0) {
    const { oid, gen } = queue.shift() as { oid: string; gen: number };
    const obj = getObject(oid);
    if (!obj) continue;
    if (obj.type === 'tag') {
      out.add(oid);
      const target = obj.data.toString('utf8').match(/^object ([0-9a-f]{40})/m)?.[1];
      if (target) queue.unshift({ oid: target, gen });
      continue;
    }
    if (obj.type !== 'commit') { out.add(oid); continue; }
    if (seenCommit.has(oid)) continue;
    seenCommit.add(oid);
    if (maxGeneration !== null && gen > maxGeneration) continue;
    out.add(oid);
    addTree(parseCommit(obj.data).tree);
    if (maxGeneration === null || gen < maxGeneration) {
      for (const parent of parseCommit(obj.data).parents) queue.push({ oid: parent, gen: gen + 1 });
    }
  }
  return out;
}

/** Generation (1 = tip) of every commit reachable from tips, breadth-first minimum. */
function generationsOf(tips: string[]): Map<string, number> {
  const gens = new Map<string, number>();
  const queue: Array<{ oid: string; gen: number }> = [];
  for (const tip of tips) {
    const obj = getObject(tip);
    if (obj && obj.type === 'tag') {
      const target = obj.data.toString('utf8').match(/^object ([0-9a-f]{40})/m)?.[1];
      if (target) queue.push({ oid: target, gen: 1 });
    } else {
      queue.push({ oid: tip, gen: 1 });
    }
  }
  while (queue.length > 0) {
    const { oid, gen } = queue.shift() as { oid: string; gen: number };
    if (gens.has(oid)) continue;
    const obj = getObject(oid);
    if (!obj || obj.type !== 'commit') continue;
    gens.set(oid, gen);
    for (const parent of parseCommit(obj.data).parents) queue.push({ oid: parent, gen: gen + 1 });
  }
  return gens;
}

function peeledCommit(oid: string): string {
  let current = oid;
  for (let i = 0; i < 16; i += 1) {
    const obj = getObject(current);
    if (!obj || obj.type !== 'tag') return current;
    const target = obj.data.toString('utf8').match(/^object ([0-9a-f]{40})/m)?.[1];
    if (!target) return current;
    current = target;
  }
  return current;
}

// --------------------------------------------------------------------------- the forge (supervisor) and repo actors

interface IssueRec {
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  seq: number;
  comments: Array<{ id: number; body: string }>;
}

interface PullRec {
  number: number;
  title: string;
  body: string;
  head: string;
  base: string;
  headSha: string;
  state: 'open' | 'closed';
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  seq: number;
}

interface RepoRec {
  id: number;
  name: string;
  owner: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  refs: Map<string, string>;
  labels: Map<string, { name: string; color: string }>;
  issues: Map<number, IssueRec>;
  pulls: Map<number, PullRec>;
  nextNumber: number;
  seq: number;
}

/** One repository actor: its record plus the mailbox (queue) every operation is posted through. */
class RepoActor {
  readonly repo: RepoRec;
  private tail: Promise<unknown> = Promise.resolve();

  constructor(repo: RepoRec) {
    this.repo = repo;
  }

  /** Post a message to this actor's mailbox; messages run one at a time, in posting order. */
  post<T>(message: (repo: RepoRec) => T | Promise<T>): Promise<T> {
    const run = this.tail.then(() => message(this.repo));
    this.tail = run.then(() => undefined, () => undefined);
    return run as Promise<T>;
  }
}

/** The supervisor: the actor registry plus repository lifecycle. The object pool above is its other ward. */
class Forge {
  private actors = new Map<string, RepoActor>();
  private nextRepoId = 5000;

  createRepo(name: string, description: string, isPrivate: boolean, defaultBranch: string): RepoRec | null {
    const key = `${OWNER}/${name}`;
    if (this.actors.has(key)) return null;
    const repo: RepoRec = {
      id: this.nextRepoId,
      name,
      owner: OWNER,
      description,
      isPrivate,
      defaultBranch: defaultBranch === '' ? 'main' : defaultBranch,
      refs: new Map(),
      labels: new Map(),
      issues: new Map(),
      pulls: new Map(),
      nextNumber: 1,
      seq: 0,
    };
    this.nextRepoId += 1;
    this.actors.set(key, new RepoActor(repo));
    return repo;
  }

  actor(owner: string, name: string): RepoActor | null {
    if (owner !== OWNER) return null;
    return this.actors.get(`${owner}/${name}`) ?? null;
  }

  findById(id: number): RepoActor | null {
    for (const actor of this.actors.values()) if (actor.repo.id === id) return actor;
    return null;
  }

  allRepos(): RepoRec[] {
    return [...this.actors.values()].map((a) => a.repo).sort((a, b) => a.id - b.id);
  }

  remove(owner: string, name: string): boolean {
    if (owner !== OWNER) return false;
    return this.actors.delete(`${owner}/${name}`);
  }
}

const forge = new Forge();

// --------------------------------------------------------------------------- commits and merges (actor-side helpers; call inside a mailbox message)

function branchRef(branch: string): string {
  return `refs/heads/${branch}`;
}

function tipOf(repo: RepoRec, branch: string): string | null {
  return repo.refs.get(branchRef(branch)) ?? null;
}

/** Create a commit over `files` on `branch` and move the branch. Returns the commit id. */
function commitFiles(repo: RepoRec, branch: string, files: Map<string, FileEntry>, message: string): string {
  const parent = tipOf(repo, branch);
  const tree = buildTree(files);
  commitSeq += 1;
  const stamp = EPOCH + commitSeq;
  const lines: string[] = [`tree ${tree}`];
  if (parent) lines.push(`parent ${parent}`);
  lines.push(`author ${OWNER_NAME} <${OWNER_EMAIL}> ${stamp} +0000`);
  lines.push(`committer ${OWNER_NAME} <${OWNER_EMAIL}> ${stamp} +0000`);
  lines.push('');
  lines.push(message.endsWith('\n') ? message.slice(0, -1) : message);
  const sha = storeObject('commit', Buffer.from(lines.join('\n'), 'utf8'));
  repo.refs.set(branchRef(branch), sha);
  repo.seq += 1;
  return sha;
}

interface ChangedFile { filename: string; status: string; additions: number; deletions: number; changes: number }

function lineCount(sha: string | undefined): number {
  if (!sha) return 0;
  const obj = getObject(sha);
  if (!obj) return 0;
  const text = obj.data.toString('utf8');
  if (text === '') return 0;
  return text.split('\n').length;
}

/** The changed paths between two commits' trees. */
function diffFiles(fromCommit: string | null, toCommit: string | null): ChangedFile[] {
  const from = fromCommit ? filesAt(fromCommit).files : new Map<string, FileEntry>();
  const to = toCommit ? filesAt(toCommit).files : new Map<string, FileEntry>();
  const out: ChangedFile[] = [];
  const paths = new Set<string>([...from.keys(), ...to.keys()]);
  for (const path of [...paths].sort()) {
    const a = from.get(path);
    const b = to.get(path);
    if (a && b && a.sha === b.sha) continue;
    if (!a && b) out.push({ filename: path, status: 'added', additions: lineCount(b.sha), deletions: 0, changes: lineCount(b.sha) });
    else if (a && !b) out.push({ filename: path, status: 'removed', additions: 0, deletions: lineCount(a.sha), changes: lineCount(a.sha) });
    else if (a && b) out.push({ filename: path, status: 'modified', additions: lineCount(b.sha), deletions: lineCount(a.sha), changes: lineCount(b.sha) + lineCount(a.sha) });
  }
  return out;
}

/** Compute the squash result of a pull: the merged file map, or null when the branches conflict. */
function squashResult(repo: RepoRec, pull: PullRec): Map<string, FileEntry> | null {
  const baseTip = tipOf(repo, pull.base);
  const headTip = repo.refs.get(branchRef(pull.head)) ?? pull.headSha;
  if (!baseTip || !headTip) return null;
  const base = mergeBase(baseTip, headTip);
  if (!base) return null;
  const baseFiles = filesAt(baseTip).files;
  const headFiles = filesAt(headTip).files;
  const originFiles = filesAt(base).files;
  const result = new Map<string, FileEntry>(baseFiles);
  const paths = new Set<string>([...originFiles.keys(), ...headFiles.keys()]);
  for (const path of paths) {
    const origin = originFiles.get(path);
    const head = headFiles.get(path);
    const current = baseFiles.get(path);
    const headChanged = (origin?.sha ?? null) !== (head?.sha ?? null);
    if (!headChanged) continue;
    const baseChanged = (origin?.sha ?? null) !== (current?.sha ?? null);
    if (baseChanged && (current?.sha ?? null) !== (head?.sha ?? null)) return null; // both sides moved it, differently
    if (head) result.set(path, head);
    else result.delete(path);
  }
  return result;
}

/** Squash-merge a pull inside its actor: one new commit on the base branch. Returns its id or null on conflict. */
function mergePull(repo: RepoRec, pull: PullRec): string | null {
  const files = squashResult(repo, pull);
  if (!files) return null;
  const sha = commitFiles(repo, pull.base, files, `${pull.title}\n\nSquash-merged pull request #${pull.number}`);
  pull.state = 'closed';
  pull.merged = true;
  commitSeq += 0; // the merge commit already advanced the shared stamp inside commitFiles
  pull.mergedAt = isoAt(commitSeq);
  pull.mergeCommitSha = sha;
  return sha;
}

function pullConflicted(repo: RepoRec, pull: PullRec): boolean {
  if (pull.state !== 'open') return false;
  return squashResult(repo, pull) === null;
}

// --------------------------------------------------------------------------- global ids and serializers

function globalId(kind: string, payload: string): string {
  return Buffer.from(`${kind}:${payload}`, 'utf8').toString('base64');
}

function parseGlobalId(id: string): { kind: string; payload: string } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const colon = text.indexOf(':');
    if (colon < 0) return null;
    return { kind: text.slice(0, colon), payload: text.slice(colon + 1) };
  } catch {
    return null;
  }
}

function repoJson(repo: RepoRec): Record<string, unknown> {
  return {
    id: repo.id,
    node_id: globalId('Repository', String(repo.id)),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: OWNER_ID, type: 'User', node_id: globalId('User', String(OWNER_ID)) },
    private: repo.isPrivate,
    description: repo.description,
    default_branch: repo.defaultBranch,
    html_url: `/${repo.owner}/${repo.name}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    git_url: `/${repo.owner}/${repo.name}.git`,
    has_issues: true,
    has_projects: true,
    has_wiki: true,
    open_issues_count: [...repo.issues.values()].filter((i) => i.state === 'open').length,
    created_at: isoAt(repo.id),
    updated_at: isoAt(repo.id + repo.seq),
    fork: false,
    archived: false,
    disabled: false,
    visibility: repo.isPrivate ? 'private' : 'public',
  };
}

function labelJson(name: string, color: string): Record<string, unknown> {
  return { id: 0, node_id: globalId('Label', name), name, color, description: null, default: false };
}

function issueJson(repo: RepoRec, issue: IssueRec): Record<string, unknown> {
  return {
    id: repo.id * 100000 + issue.number,
    node_id: globalId('Issue', `${repo.id}:${issue.number}`),
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => labelJson(name, repo.labels.get(name)?.color ?? 'ededed')),
    user: { login: OWNER, id: OWNER_ID, type: 'User' },
    comments: issue.comments.length,
    created_at: isoAt(issue.seq),
    updated_at: isoAt(issue.seq),
    closed_at: issue.state === 'closed' ? isoAt(issue.seq + 1) : null,
    html_url: `/${repo.owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${repo.owner}/${repo.name}`,
  };
}

function pullJson(repo: RepoRec, pull: PullRec): Record<string, unknown> {
  const headTip = repo.refs.get(branchRef(pull.head)) ?? pull.headSha;
  const baseTip = tipOf(repo, pull.base) ?? ZERO_OID;
  return {
    id: repo.id * 100000 + pull.number,
    node_id: globalId('PullRequest', `${repo.id}:${pull.number}`),
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    head: {
      ref: pull.head,
      sha: headTip,
      label: `${repo.owner}:${pull.head}`,
      repo: { id: repo.id, name: repo.name, full_name: `${repo.owner}/${repo.name}` },
    },
    base: {
      ref: pull.base,
      sha: baseTip,
      label: `${repo.owner}:${pull.base}`,
      repo: { id: repo.id, name: repo.name, full_name: `${repo.owner}/${repo.name}` },
    },
    user: { login: OWNER, id: OWNER_ID, type: 'User' },
    created_at: isoAt(pull.seq),
    updated_at: isoAt(pull.seq),
    closed_at: pull.state === 'closed' ? pull.mergedAt ?? isoAt(pull.seq + 1) : null,
    html_url: `/${repo.owner}/${repo.name}/pull/${pull.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}`,
  };
}

// --------------------------------------------------------------------------- HTTP plumbing

interface Reply {
  status: number;
  body?: unknown;
  headers?: Record<string, string>;
  empty?: boolean;
}

function errReply(status: number, message: string): Reply {
  return { status, body: { message } };
}

function notFound(): Reply {
  return errReply(404, 'Not Found');
}

function sendJson(res: ServerResponse, reply: Reply): void {
  requestSeq += 1;
  const headers: Record<string, string> = {
    'x-github-request-id': `req-${requestSeq.toString(36)}-${randomUUID().slice(0, 8)}`,
    ...(reply.headers ?? {}),
  };
  if (reply.empty || reply.status === 204) {
    res.writeHead(reply.status, headers);
    res.end();
    return;
  }
  const text = `${JSON.stringify(reply.body ?? {})}\n`;
  res.writeHead(reply.status, { 'content-type': JSON_TYPE, 'content-length': Buffer.byteLength(text), ...headers });
  res.end(text);
}

function sendRaw(res: ServerResponse, status: number, contentType: string, body: Buffer): void {
  requestSeq += 1;
  res.writeHead(status, {
    'content-type': contentType,
    'content-length': body.length,
    'x-github-request-id': `req-${requestSeq.toString(36)}-${randomUUID().slice(0, 8)}`,
  });
  res.end(body);
}

async function readBody(req: IncomingMessage): Promise<Buffer> {
  const chunks: Buffer[] = [];
  for await (const chunk of req) chunks.push(Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk as Uint8Array));
  return Buffer.concat(chunks);
}

function authed(req: IncomingMessage): boolean {
  if (TOKEN === '') return true;
  return (req.headers.authorization ?? '') === `Bearer ${TOKEN}`;
}

function pageParams(url: URL): { page: number; perPage: number } {
  const page = Math.max(1, parseInt(url.searchParams.get('page') ?? '1', 10) || 1);
  const perPage = Math.min(100, Math.max(1, parseInt(url.searchParams.get('per_page') ?? '30', 10) || 30));
  return { page, perPage };
}

function linkHeader(req: IncomingMessage, url: URL, page: number, perPage: number, total: number): string | undefined {
  const lastPage = Math.max(1, Math.ceil(total / perPage));
  if (page >= lastPage) return undefined;
  const host = req.headers.host ?? 'localhost';
  const make = (p: number): string => {
    const q = new URLSearchParams(url.searchParams);
    q.set('page', String(p));
    q.set('per_page', String(perPage));
    return `http://${host}${url.pathname}?${q.toString()}`;
  };
  return `<${make(page + 1)}>; rel="next", <${make(lastPage)}>; rel="last"`;
}

// --------------------------------------------------------------------------- REST v3

type Json = Record<string, unknown>;

function asRecord(value: unknown): Json {
  return typeof value === 'object' && value !== null && !Array.isArray(value) ? (value as Json) : {};
}

function str(value: unknown): string {
  return typeof value === 'string' ? value : '';
}

async function restRoot(): Promise<Reply> {
  return {
    status: 200,
    headers: { 'x-oauth-scopes': 'repo, read:org' },
    body: {
      current_user_url: '/api/v3/user',
      current_user_repositories_url: '/api/v3/user/repos',
      repository_url: '/api/v3/repos/{owner}/{repo}',
      rate_limit_url: '/api/v3/rate_limit',
      emojis_url: '/api/v3/emojis',
      issue_search_url: '/api/v3/search/issues',
    },
  };
}

async function createRepoReply(body: Json): Promise<Reply> {
  const name = str(body.name);
  if (name === '') return errReply(422, 'Repository creation failed: name is required');
  const created = forge.createRepo(name, str(body.description), body.private === true, str(body.default_branch));
  if (!created) return errReply(422, 'Repository already exists');
  return { status: 201, body: repoJson(created) };
}

async function contentsPut(repo: RepoRec, segments: string[], body: Json): Promise<Reply> {
  const path = segments.join('/');
  if (path === '') return errReply(422, 'Validation Failed: path is required');
  const branch = str(body.branch) || repo.defaultBranch;
  const refExists = repo.refs.has(branchRef(branch));
  if (!refExists && repo.refs.size > 0 && branch !== repo.defaultBranch) return errReply(404, 'Branch not found');
  const tip = tipOf(repo, branch);
  const { files } = tip ? filesAt(tip) : { files: new Map<string, FileEntry>() };
  const existing = files.get(path);
  const shaGiven = str(body.sha);
  if (existing && shaGiven !== '' && shaGiven !== existing.sha) return errReply(409, 'Conflict: sha does not match the current file');
  if (existing && shaGiven === '') return errReply(422, 'Validation Failed: sha is required when updating a file');
  const content = Buffer.from(str(body.content), 'base64');
  const blobSha = storeObject('blob', content);
  files.set(path, { sha: blobSha, mode: '100644' });
  const message = str(body.message) || 'Update file';
  const commitSha = commitFiles(repo, branch, files, message);
  return {
    status: existing ? 200 : 201,
    body: {
      content: { type: 'file', name: path.split('/').pop() ?? path, path, sha: blobSha, size: content.length, encoding: 'base64' },
      commit: { sha: commitSha, message, author: { name: OWNER_NAME, email: OWNER_EMAIL }, committer: { name: OWNER_NAME, email: OWNER_EMAIL } },
    },
  };
}

function contentsGet(repo: RepoRec, segments: string[], url: URL): Reply {
  const path = segments.join('/');
  const refParam = url.searchParams.get('ref') ?? '';
  let commit: string | null = null;
  if (refParam !== '' && /^[0-9a-f]{40}$/.test(refParam) && getObject(refParam)?.type === 'commit') commit = refParam;
  else if (refParam !== '') commit = repo.refs.get(branchRef(refParam)) ?? null;
  else commit = tipOf(repo, repo.defaultBranch);
  if (!commit) {
    if (path === '') return { status: 200, body: [] };
    return notFound();
  }
  const { files, dirs } = filesAt(commit);
  if (path !== '') {
    const file = files.get(path);
    if (file) {
      const obj = getObject(file.sha);
      const data = obj?.data ?? Buffer.alloc(0);
      return {
        status: 200,
        body: {
          type: 'file', name: path.split('/').pop() ?? path, path, sha: file.sha, size: data.length,
          encoding: 'base64', content: data.toString('base64'),
        },
      };
    }
    if (!dirs.has(path)) return notFound();
  }
  const prefix = path === '' ? '' : `${path}/`;
  const entries: Array<Record<string, unknown>> = [];
  for (const [dirPath, sha] of dirs) {
    if (!dirPath.startsWith(prefix)) continue;
    const rest = dirPath.slice(prefix.length);
    if (rest !== '' && !rest.includes('/')) entries.push({ type: 'dir', name: rest, path: dirPath, sha, size: 0 });
  }
  for (const [filePath, file] of files) {
    if (!filePath.startsWith(prefix)) continue;
    const rest = filePath.slice(prefix.length);
    if (rest !== '' && !rest.includes('/')) {
      const obj = getObject(file.sha);
      entries.push({ type: 'file', name: rest, path: filePath, sha: file.sha, size: obj?.data.length ?? 0 });
    }
  }
  entries.sort((a, b) => String(a.name) < String(b.name) ? -1 : 1);
  return { status: 200, body: entries };
}

function contentsDelete(repo: RepoRec, segments: string[], body: Json): Reply {
  const path = segments.join('/');
  const branch = str(body.branch) || repo.defaultBranch;
  const tip = tipOf(repo, branch);
  if (!tip) return notFound();
  const { files } = filesAt(tip);
  const existing = files.get(path);
  if (!existing) return notFound();
  const shaGiven = str(body.sha);
  if (shaGiven !== '' && shaGiven !== existing.sha) return errReply(409, 'Conflict: sha does not match the current file');
  files.delete(path);
  const commitSha = commitFiles(repo, branch, files, str(body.message) || 'Delete file');
  return { status: 200, body: { content: null, commit: { sha: commitSha } } };
}

function createIssueReply(repo: RepoRec, body: Json): Reply {
  const rawLabels = Array.isArray(body.labels) ? body.labels : [];
  const names: string[] = [];
  for (const entry of rawLabels) {
    const name = typeof entry === 'string' ? entry : str(asRecord(entry).name);
    if (name === '') continue;
    if (!repo.labels.has(name)) return errReply(422, `Validation Failed: label "${name}" does not exist`);
    names.push(name);
  }
  commitSeq += 1;
  const issue: IssueRec = {
    number: repo.nextNumber,
    title: str(body.title),
    body: typeof body.body === 'string' ? body.body : '',
    state: 'open',
    labels: names,
    seq: commitSeq,
    comments: [],
  };
  repo.nextNumber += 1;
  repo.issues.set(issue.number, issue);
  return { status: 201, body: issueJson(repo, issue) };
}

function listIssuesReply(repo: RepoRec, url: URL): Reply {
  const state = url.searchParams.get('state') ?? 'open';
  let list = [...repo.issues.values()];
  if (state === 'open') list = list.filter((i) => i.state === 'open');
  else if (state === 'closed') list = list.filter((i) => i.state === 'closed');
  const direction = url.searchParams.get('direction') ?? 'desc';
  list.sort((a, b) => (direction === 'asc' ? a.number - b.number : b.number - a.number));
  const { page, perPage } = pageParams(url);
  const slice = list.slice((page - 1) * perPage, page * perPage);
  return { status: 200, body: slice.map((i) => issueJson(repo, i)) };
}

function createPullReply(repo: RepoRec, body: Json): Reply {
  const cleanRef = (value: string): string => (value.includes(':') ? value.slice(value.indexOf(':') + 1) : value);
  const head = cleanRef(str(body.head));
  const base = cleanRef(str(body.base)) || repo.defaultBranch;
  const headTip = repo.refs.get(branchRef(head));
  if (!headTip) return errReply(422, 'Validation Failed: head branch does not exist');
  if (!repo.refs.has(branchRef(base))) return errReply(422, 'Validation Failed: base branch does not exist');
  for (const existing of repo.pulls.values()) {
    if (existing.state === 'open' && existing.head === head && existing.base === base) {
      return errReply(422, 'Validation Failed: a pull request already exists for this head and base');
    }
  }
  commitSeq += 1;
  const pull: PullRec = {
    number: repo.nextNumber,
    title: str(body.title),
    body: typeof body.body === 'string' ? body.body : '',
    head,
    base,
    headSha: headTip,
    state: 'open',
    merged: false,
    mergedAt: null,
    mergeCommitSha: null,
    seq: commitSeq,
  };
  repo.nextNumber += 1;
  repo.pulls.set(pull.number, pull);
  return { status: 201, body: pullJson(repo, pull) };
}

function listPullsReply(repo: RepoRec, url: URL): Reply {
  const state = url.searchParams.get('state') ?? 'open';
  let list = [...repo.pulls.values()];
  if (state === 'open') list = list.filter((p) => p.state === 'open');
  else if (state === 'closed') list = list.filter((p) => p.state === 'closed');
  list.sort((a, b) => a.number - b.number);
  const { page, perPage } = pageParams(url);
  const slice = list.slice((page - 1) * perPage, page * perPage);
  return { status: 200, body: slice.map((p) => pullJson(repo, p)) };
}

async function handleRepoRoute(req: IncomingMessage, url: URL, segments: string[], body: Json, rawBody: Buffer): Promise<Reply> {
  const method = req.method ?? 'GET';
  const owner = segments[0] ?? '';
  const name = segments[1] ?? '';
  const rest = segments.slice(2);

  if (rest.length === 0) {
    if (method === 'GET') {
      const actor = forge.actor(owner, name);
      if (!actor) return notFound();
      return actor.post((repo) => ({ status: 200, body: repoJson(repo) }));
    }
    if (method === 'PATCH') {
      const actor = forge.actor(owner, name);
      if (!actor) return notFound();
      return actor.post((repo) => {
        if (typeof body.description === 'string') repo.description = body.description;
        if (typeof body.name === 'string' && body.name !== '') repo.name = body.name;
        if (typeof body.private === 'boolean') repo.isPrivate = body.private;
        if (typeof body.default_branch === 'string' && body.default_branch !== '') repo.defaultBranch = body.default_branch;
        repo.seq += 1;
        return { status: 200, body: repoJson(repo) };
      });
    }
    if (method === 'DELETE') {
      if (!forge.remove(owner, name)) return notFound();
      return { status: 204, empty: true };
    }
    return notFound();
  }

  const actor = forge.actor(owner, name);
  if (!actor) return notFound();

  return actor.post(async (repo): Promise<Reply> => {
    const [head, ...tail] = rest as [string, ...string[]];

    if (head === 'contents') {
      if (method === 'PUT') return contentsPut(repo, tail, body);
      if (method === 'GET') return contentsGet(repo, tail, url);
      if (method === 'DELETE') return contentsDelete(repo, tail, body);
      return notFound();
    }

    if (head === 'labels') {
      if (method === 'POST') {
        const labelName = str(body.name);
        if (labelName === '') return errReply(422, 'Validation Failed: name is required');
        if (repo.labels.has(labelName)) return errReply(422, 'Validation Failed: label already exists');
        labelSeq += 1;
        const color = str(body.color) || 'ededed';
        repo.labels.set(labelName, { name: labelName, color });
        const json = labelJson(labelName, color);
        json.id = labelSeq;
        return { status: 201, body: json };
      }
      if (method === 'GET') return { status: 200, body: [...repo.labels.values()].map((l) => labelJson(l.name, l.color)) };
      return notFound();
    }

    if (head === 'issues') {
      if (tail.length === 0) {
        if (method === 'POST') return createIssueReply(repo, body);
        if (method === 'GET') return listIssuesReply(repo, url);
        return notFound();
      }
      const number = parseInt(tail[0] ?? '', 10);
      const issue = Number.isInteger(number) ? repo.issues.get(number) : undefined;
      if (tail.length === 1) {
        if (!issue) return notFound();
        if (method === 'GET') return { status: 200, body: issueJson(repo, issue) };
        if (method === 'PATCH') {
          if (body.state === 'closed' || body.state === 'open') issue.state = body.state;
          if (typeof body.title === 'string') issue.title = body.title;
          if (typeof body.body === 'string') issue.body = body.body;
          return { status: 200, body: issueJson(repo, issue) };
        }
        return notFound();
      }
      if (tail.length === 2 && tail[1] === 'comments') {
        if (!issue) return notFound();
        if (method === 'POST') {
          commentSeq += 1;
          const comment = { id: commentSeq, body: str(body.body) };
          issue.comments.push(comment);
          return { status: 201, body: { id: comment.id, body: comment.body, user: { login: OWNER, id: OWNER_ID, type: 'User' }, created_at: isoAt(commentSeq) } };
        }
        if (method === 'GET') {
          return { status: 200, body: issue.comments.map((c) => ({ id: c.id, body: c.body, user: { login: OWNER, id: OWNER_ID, type: 'User' }, created_at: isoAt(c.id) })) };
        }
        return notFound();
      }
      return notFound();
    }

    if (head === 'pulls') {
      if (tail.length === 0) {
        if (method === 'POST') return createPullReply(repo, body);
        if (method === 'GET') return listPullsReply(repo, url);
        return notFound();
      }
      const number = parseInt(tail[0] ?? '', 10);
      const pull = Number.isInteger(number) ? repo.pulls.get(number) : undefined;
      if (tail.length === 1) {
        if (!pull) return notFound();
        if (method === 'GET') return { status: 200, body: pullJson(repo, pull) };
        if (method === 'PATCH') {
          if (body.state === 'closed' || body.state === 'open') pull.state = body.state;
          if (typeof body.title === 'string') pull.title = body.title;
          if (typeof body.body === 'string') pull.body = body.body;
          return { status: 200, body: pullJson(repo, pull) };
        }
        return notFound();
      }
      if (tail.length === 2 && tail[1] === 'files') {
        if (!pull) return notFound();
        if (method !== 'GET') return notFound();
        const headTip = repo.refs.get(branchRef(pull.head)) ?? pull.headSha;
        const baseTip = tipOf(repo, pull.base);
        const origin = baseTip ? mergeBase(baseTip, headTip) : null;
        return { status: 200, body: diffFiles(origin, headTip) };
      }
      if (tail.length === 2 && tail[1] === 'merge') {
        if (!pull) return notFound();
        if (method !== 'PUT' && method !== 'POST') return notFound();
        if (pull.merged) return errReply(405, 'Pull Request is not mergeable: already merged');
        if (pull.state !== 'open') return errReply(405, 'Pull Request is not mergeable: closed');
        const sha = mergePull(repo, pull);
        if (!sha) return errReply(405, 'Pull Request is not mergeable: conflict');
        return { status: 200, body: { sha, merged: true, message: 'Pull Request successfully merged' } };
      }
      return notFound();
    }

    if (head === 'git' && tail[0] === 'refs') {
      if (tail.length === 1 && method === 'POST') {
        const ref = str(body.ref);
        const sha = str(body.sha);
        if (!ref.startsWith('refs/') || !getObject(sha)) return errReply(422, 'Validation Failed: invalid ref or sha');
        if (repo.refs.has(ref)) return errReply(422, 'Validation Failed: reference already exists');
        repo.refs.set(ref, sha);
        const obj = getObject(sha) as GitObj;
        return { status: 201, body: { ref, node_id: globalId('Ref', ref), object: { sha, type: obj.type } } };
      }
      if (method === 'GET' && tail.length >= 2) {
        const ref = `refs/${tail.slice(1).join('/')}`;
        const sha = repo.refs.get(ref);
        if (!sha) return notFound();
        const obj = getObject(sha) as GitObj;
        return { status: 200, body: { ref, node_id: globalId('Ref', ref), object: { sha, type: obj.type } } };
      }
      return notFound();
    }

    if (head === 'branches') {
      if (tail.length === 0 && method === 'GET') {
        const branches = [...repo.refs.entries()]
          .filter(([ref]) => ref.startsWith('refs/heads/'))
          .map(([ref, sha]) => ({ name: ref.slice('refs/heads/'.length), commit: { sha }, protected: false }))
          .sort((a, b) => (a.name < b.name ? -1 : 1));
        return { status: 200, body: branches };
      }
      if (method === 'GET') {
        const branch = tail.join('/');
        const sha = repo.refs.get(branchRef(branch));
        if (!sha) return notFound();
        return { status: 200, body: { name: branch, commit: { sha }, protected: false } };
      }
      return notFound();
    }

    if (head === 'commits') {
      if (tail.length === 0 && method === 'GET') {
        const shaParam = url.searchParams.get('sha') ?? '';
        let tip: string | null = null;
        if (shaParam === '') tip = tipOf(repo, repo.defaultBranch);
        else if (/^[0-9a-f]{40}$/.test(shaParam) && getObject(shaParam)?.type === 'commit') tip = shaParam;
        else tip = repo.refs.get(branchRef(shaParam)) ?? null;
        if (!tip) return { status: 200, body: [] };
        const list = ancestorsOf(tip).map((sha) => {
          const obj = getObject(sha) as GitObj;
          const info = parseCommit(obj.data);
          return {
            sha,
            commit: {
              message: info.message,
              tree: { sha: info.tree },
              author: { name: OWNER_NAME, email: OWNER_EMAIL, date: isoAt(0) },
              committer: { name: OWNER_NAME, email: OWNER_EMAIL, date: isoAt(0) },
            },
            parents: info.parents.map((p) => ({ sha: p })),
          };
        });
        const perPageParam = url.searchParams.get('per_page');
        if (perPageParam) {
          const { page, perPage } = pageParams(url);
          return { status: 200, body: list.slice((page - 1) * perPage, page * perPage) };
        }
        return { status: 200, body: list };
      }
      if (tail.length === 1 && method === 'GET') {
        const sha = tail[0] as string;
        const obj = getObject(sha);
        if (!obj || obj.type !== 'commit') return notFound();
        const info = parseCommit(obj.data);
        return { status: 200, body: { sha, commit: { message: info.message, tree: { sha: info.tree } }, parents: info.parents.map((p) => ({ sha: p })) } };
      }
      return notFound();
    }

    void rawBody;
    return notFound();
  });
}

async function handleRest(req: IncomingMessage, url: URL, segments: string[], bodyText: string): Promise<Reply> {
  const method = req.method ?? 'GET';
  // segments are the path after /api/v3
  let body: Json = {};
  if (bodyText.trim() !== '') {
    try {
      const parsed: unknown = JSON.parse(bodyText);
      body = asRecord(parsed);
    } catch {
      return errReply(400, 'Malformed JSON body');
    }
  }
  if (segments.length === 0) {
    if (method === 'GET') return restRoot();
    return notFound();
  }
  const [first, ...restSegs] = segments as [string, ...string[]];
  if (first === 'meta' && restSegs.length === 0 && method === 'GET') {
    return { status: 200, body: { verifiable_password_authentication: false, installed_version: `1.0.0-sage-owl-${VERSION}`, enterprise: false } };
  }
  if (first === 'user' && restSegs.length === 0 && method === 'GET') {
    return { status: 200, body: { login: OWNER, id: OWNER_ID, type: 'User', name: OWNER_NAME, email: OWNER_EMAIL, node_id: globalId('User', String(OWNER_ID)) } };
  }
  if (first === 'user' && restSegs.length === 1 && restSegs[0] === 'repos') {
    if (method === 'GET') {
      const all = forge.allRepos();
      const { page, perPage } = pageParams(url);
      const slice = all.slice((page - 1) * perPage, page * perPage);
      const link = linkHeader(req, url, page, perPage, all.length);
      return { status: 200, body: slice.map((r) => repoJson(r)), headers: link ? { link } : {} };
    }
    if (method === 'POST') return createRepoReply(body);
    return notFound();
  }
  if (first === 'repos' && restSegs.length >= 2) {
    return handleRepoRoute(req, url, restSegs, body, Buffer.from(bodyText, 'utf8'));
  }
  return notFound();
}

// --------------------------------------------------------------------------- git smart HTTP

interface RefSnapshot { refs: Array<[string, string]>; defaultBranch: string }

function snapshotOf(repo: RepoRec): RefSnapshot {
  return { refs: [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1)), defaultBranch: repo.defaultBranch };
}

function headTipOf(snap: RefSnapshot): string | null {
  return snap.refs.find(([ref]) => ref === branchRef(snap.defaultBranch))?.[1] ?? null;
}

function boundaryClosure(oid: string): Set<string> {
  return reachableObjects([oid], 1);
}

interface PackPlan { oids: string[]; shallow: string[]; unshallow: string[] }

function planPack(wants: string[], haves: string[], shallowList: string[], depth: number | null): PackPlan {
  const shallowSet = new Set(shallowList);
  const included = reachableObjects(wants, depth);
  const held = new Set<string>();
  for (const have of haves) {
    const part = shallowSet.has(have) ? boundaryClosure(have) : reachableObjects([have], null);
    for (const oid of part) held.add(oid);
  }
  for (const boundary of shallowList) {
    if (haves.includes(boundary)) continue;
    for (const oid of boundaryClosure(boundary)) held.add(oid);
  }
  const oids = [...included].filter((oid) => !held.has(oid));
  const shallow: string[] = [];
  const unshallow: string[] = [];
  if (depth !== null) {
    const gens = generationsOf(wants);
    for (const [oid, gen] of gens) {
      if (gen === depth) {
        const obj = getObject(oid);
        if (obj && obj.type === 'commit' && parseCommit(obj.data).parents.length > 0) shallow.push(oid);
      }
    }
    for (const boundary of shallowList) {
      const gen = gens.get(boundary);
      if (gen !== undefined && gen < depth) unshallow.push(boundary);
    }
  }
  return { oids, shallow, unshallow };
}

function sidebandPackets(pack: Buffer): Buffer[] {
  const out: Buffer[] = [];
  const CHUNK = 60000;
  if (pack.length === 0) {
    out.push(pkt(Buffer.concat([Buffer.from([1]), pack])));
    return out;
  }
  for (let pos = 0; pos < pack.length; pos += CHUNK) {
    out.push(pkt(Buffer.concat([Buffer.from([1]), pack.subarray(pos, pos + CHUNK)])));
  }
  return out;
}

function gitAdvertisement(snap: RefSnapshot, service: string, version2: boolean): Buffer {
  if (service === 'git-upload-pack' && version2) {
    return Buffer.concat([
      pkt('version 2\n'),
      pkt('agent=sage-owl-forge/1.0\n'),
      pkt('ls-refs=unborn peel symrefs\n'),
      pkt('fetch=shallow wait-for-done\n'),
      pkt('object-format=sha1\n'),
      PKT_FLUSH,
    ]);
  }
  const isUpload = service === 'git-upload-pack';
  const caps = isUpload
    ? `multi_ack_detailed side-band-64k ofs-delta shallow thin-pack agent=sage-owl-forge/1.0 symref=HEAD:${branchRef(snap.defaultBranch)}`
    : `report-status side-band-64k delete-refs ofs-delta agent=sage-owl-forge/1.0 symref=HEAD:${branchRef(snap.defaultBranch)}`;
  const parts: Buffer[] = [pkt(`# service=${service}\n`), PKT_FLUSH];
  const headTip = headTipOf(snap);
  const lines: string[] = [];
  if (headTip) lines.push(`${headTip} HEAD`);
  else lines.push(`${ZERO_OID} capabilities^{}`);
  for (const [ref, oid] of snap.refs) {
    lines.push(`${oid} ${ref}`);
    const obj = getObject(oid);
    if (obj && obj.type === 'tag') lines.push(`${peeledCommit(oid)} ${ref}^{}`);
  }
  lines.forEach((line, index) => {
    parts.push(pkt(index === 0 ? `${line}\0${caps}\n` : `${line}\n`));
  });
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function lsRefsReply(snap: RefSnapshot, args: string[]): Buffer {
  let peel = false;
  let symrefs = false;
  let unborn = false;
  const prefixes: string[] = [];
  for (const arg of args) {
    if (arg === 'peel') peel = true;
    else if (arg === 'symrefs') symrefs = true;
    else if (arg === 'unborn') unborn = true;
    else if (arg.startsWith('ref-prefix ')) prefixes.push(arg.slice('ref-prefix '.length));
  }
  const matches = (name: string): boolean => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
  const lines: string[] = [];
  const headTip = headTipOf(snap);
  if (matches('HEAD')) {
    if (headTip) lines.push(`${headTip} HEAD${symrefs ? ` symref-target:${branchRef(snap.defaultBranch)}` : ''}`);
    else if (unborn) lines.push(`unborn HEAD${symrefs ? ` symref-target:${branchRef(snap.defaultBranch)}` : ''}`);
  }
  for (const [ref, oid] of snap.refs) {
    if (!matches(ref)) continue;
    let line = `${oid} ${ref}`;
    const obj = getObject(oid);
    if (peel && obj && obj.type === 'tag') line += ` peeled:${peeledCommit(oid)}`;
    lines.push(line);
  }
  return Buffer.concat([...lines.map((l) => pkt(`${l}\n`)), PKT_FLUSH]);
}

function fetchReply(plan: PackPlan, version2: boolean): Buffer {
  const pack = writePack(plan.oids);
  const bands = sidebandPackets(pack);
  if (version2) {
    const parts: Buffer[] = [pkt('acknowledgments\n'), pkt('NAK\n'), PKT_DELIM];
    if (plan.shallow.length > 0 || plan.unshallow.length > 0) {
      parts.push(pkt('shallow-info\n'));
      for (const oid of plan.shallow) parts.push(pkt(`shallow ${oid}\n`));
      for (const oid of plan.unshallow) parts.push(pkt(`unshallow ${oid}\n`));
      parts.push(PKT_DELIM);
    }
    parts.push(pkt('packfile\n'));
    parts.push(...bands);
    parts.push(PKT_FLUSH);
    return Buffer.concat(parts);
  }
  const parts: Buffer[] = [];
  for (const oid of plan.shallow) parts.push(pkt(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(pkt(`unshallow ${oid}\n`));
  parts.push(pkt('NAK\n'));
  parts.push(...bands);
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

async function handleGit(req: IncomingMessage, res: ServerResponse, owner: string, repoGit: string, tail: string, url: URL, body: Buffer): Promise<void> {
  const method = req.method ?? 'GET';
  const repoName = repoGit.endsWith('.git') ? repoGit.slice(0, -4) : repoGit;
  const actor = forge.actor(owner, repoName);
  if (!actor) {
    sendRaw(res, 404, 'text/plain; charset=utf-8', Buffer.from('Repository not found\n'));
    return;
  }
  const service = url.searchParams.get('service') ?? '';

  if (method === 'GET' && tail === 'info/refs') {
    if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
      sendRaw(res, 400, 'text/plain; charset=utf-8', Buffer.from('Unknown service\n'));
      return;
    }
    const snap = await actor.post((repo) => snapshotOf(repo));
    const version2 = (req.headers['git-protocol'] ?? '').includes('version=2');
    sendRaw(res, 200, `application/x-${service}-advertisement`, gitAdvertisement(snap, service, version2));
    return;
  }

  if (method === 'POST' && tail === 'git-upload-pack') {
    try {
      const packets = decodePkts(body);
      const lines: string[] = [];
      const kinds: string[] = [];
      for (const p of packets) {
        kinds.push(p.kind);
        if (p.kind === 'data') lines.push(p.payload.toString('utf8').replace(/\n$/, ''));
      }
      void kinds;
      if (lines[0]?.startsWith('command=ls-refs')) {
        const snap = await actor.post((repo) => snapshotOf(repo));
        sendRaw(res, 200, 'application/x-git-upload-pack-result', lsRefsReply(snap, lines.slice(1)));
        return;
      }
      if (lines[0]?.startsWith('command=fetch')) {
        const wants: string[] = [];
        const haves: string[] = [];
        const shallowList: string[] = [];
        let depth: number | null = null;
        for (const line of lines.slice(1)) {
          if (line.startsWith('want ')) wants.push(line.slice(5).trim());
          else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
          else if (line.startsWith('shallow ')) shallowList.push(line.slice(8).trim());
          else if (line.startsWith('deepen ')) depth = parseInt(line.slice(7).trim(), 10) || null;
        }
        const plan = planPack(wants, haves, shallowList, depth);
        sendRaw(res, 200, 'application/x-git-upload-pack-result', fetchReply(plan, true));
        return;
      }
      // v0 fetch: wants and shallow lines, a flush, then haves and done.
      const wants: string[] = [];
      const haves: string[] = [];
      const shallowList: string[] = [];
      let depth: number | null = null;
      let afterFlush = false;
      for (const p of packets) {
        if (p.kind === 'flush') { afterFlush = true; continue; }
        if (p.kind !== 'data') continue;
        const line = p.payload.toString('utf8').replace(/\n$/, '');
        if (!afterFlush) {
          if (line.startsWith('want ')) wants.push(line.slice(5).trim().split(' ')[0] as string);
          else if (line.startsWith('shallow ')) shallowList.push(line.slice(8).trim());
          else if (line.startsWith('deepen ')) depth = parseInt(line.slice(7).trim(), 10) || null;
        } else if (line.startsWith('have ')) {
          haves.push(line.slice(5).trim());
        }
      }
      const plan = planPack(wants, haves, shallowList, depth);
      sendRaw(res, 200, 'application/x-git-upload-pack-result', fetchReply(plan, false));
      return;
    } catch {
      sendRaw(res, 400, 'text/plain; charset=utf-8', Buffer.from('Malformed upload-pack request\n'));
      return;
    }
  }

  if (method === 'POST' && tail === 'git-receive-pack') {
    try {
      // Command pkt-lines run to the first flush; everything after it is the packfile.
      let pos = 0;
      const commands: Array<{ oldOid: string; newOid: string; ref: string }> = [];
      let clientCaps = '';
      while (pos < body.length) {
        const head = body.subarray(pos, pos + 4).toString('ascii');
        if (!/^[0-9a-fA-F]{4}$/.test(head)) throw new Error('bad pkt header');
        const len = parseInt(head, 16);
        if (len === 0) { pos += 4; break; }
        if (len < 4 || pos + len > body.length) throw new Error('bad pkt length');
        const payload = body.subarray(pos + 4, pos + len).toString('utf8').replace(/\n$/, '');
        const nul = payload.indexOf('\0');
        const text = nul >= 0 ? payload.slice(0, nul) : payload;
        if (nul >= 0) clientCaps = payload.slice(nul + 1);
        const [oldOid, newOid, ref] = text.split(' ');
        if (oldOid && newOid && ref) commands.push({ oldOid, newOid, ref });
        pos += len;
      }
      const pack = body.subarray(pos);
      let unpackOk = true;
      if (pack.length > 0) {
        try { readPack(pack); } catch { unpackOk = false; }
      } else if (commands.some((c) => c.newOid !== ZERO_OID)) {
        unpackOk = false;
      }
      const results = await actor.post((repo) => commands.map((command) => {
        if (!unpackOk) return { ref: command.ref, ok: false, reason: 'unpacker error' };
        const current = repo.refs.get(command.ref) ?? ZERO_OID;
        if (command.newOid === ZERO_OID) {
          if (current === ZERO_OID) return { ref: command.ref, ok: false, reason: 'not found' };
          repo.refs.delete(command.ref);
          return { ref: command.ref, ok: true, reason: '' };
        }
        const obj = getObject(command.newOid);
        if (!obj) return { ref: command.ref, ok: false, reason: 'not found' };
        if (command.oldOid === ZERO_OID) {
          if (current !== ZERO_OID) return { ref: command.ref, ok: false, reason: 'already exists' };
        } else {
          if (current !== command.oldOid) return { ref: command.ref, ok: false, reason: 'non-fast-forward' };
          const target = obj.type === 'tag' ? peeledCommit(command.newOid) : command.newOid;
          if (current !== target && obj.type === 'commit' && !isAncestor(current, target)) {
            return { ref: command.ref, ok: false, reason: 'non-fast-forward' };
          }
          if (obj.type === 'commit' && current !== command.newOid && !isAncestor(current, command.newOid)) {
            return { ref: command.ref, ok: false, reason: 'non-fast-forward' };
          }
        }
        repo.refs.set(command.ref, command.newOid);
        return { ref: command.ref, ok: true, reason: '' };
      }));
      const reportLines: Buffer[] = [pkt(unpackOk ? 'unpack ok\n' : 'unpack error\n')];
      for (const result of results) {
        reportLines.push(pkt(result.ok ? `ok ${result.ref}\n` : `ng ${result.ref} ${result.reason}\n`));
      }
      reportLines.push(PKT_FLUSH);
      const inner = Buffer.concat(reportLines);
      let out: Buffer;
      if (clientCaps.includes('side-band-64k')) {
        const parts: Buffer[] = [];
        const CHUNK = 32000;
        for (let p = 0; p < inner.length; p += CHUNK) {
          parts.push(pkt(Buffer.concat([Buffer.from([1]), inner.subarray(p, p + CHUNK)])));
        }
        parts.push(PKT_FLUSH);
        out = Buffer.concat(parts);
      } else {
        out = inner;
      }
      sendRaw(res, 200, 'application/x-git-receive-pack-result', out);
      return;
    } catch {
      sendRaw(res, 400, 'text/plain; charset=utf-8', Buffer.from('Malformed receive-pack request\n'));
      return;
    }
  }

  sendRaw(res, 404, 'text/plain; charset=utf-8', Buffer.from('Not found\n'));
}

// --------------------------------------------------------------------------- GraphQL

type GqlValue =
  | { kind: 'var'; name: string }
  | { kind: 'scalar'; value: unknown }
  | { kind: 'list'; items: GqlValue[] }
  | { kind: 'object'; fields: Map<string, GqlValue> };

interface GqlField { name: string; alias: string | null; args: Map<string, GqlValue>; selections: GqlSelection[] }
type GqlSelection = GqlField | { kind: 'inline'; typeName: string; selections: GqlSelection[] } | { kind: 'spread'; name: string };

interface GqlOp { opType: string; name: string | null; selections: GqlSelection[] }

function tokenizeGql(text: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < text.length) {
    const ch = text[i] as string;
    if (ch === '#') { while (i < text.length && text[i] !== '\n') i += 1; continue; }
    if (/\s|,/.test(ch)) { i += 1; continue; }
    if (text.startsWith('...', i)) { tokens.push('...'); i += 3; continue; }
    if ('{}()[]:$!@|&='.includes(ch)) { tokens.push(ch); i += 1; continue; }
    if (ch === '"') {
      let j = i + 1;
      let out = '';
      while (j < text.length && text[j] !== '"') {
        if (text[j] === '\\') { out += text[j + 1] ?? ''; j += 2; }
        else { out += text[j]; j += 1; }
      }
      tokens.push(`"${out}"`);
      i = j + 1;
      continue;
    }
    const match = /^[A-Za-z0-9_.-]+/.exec(text.slice(i));
    if (match) { tokens.push(match[0]); i += match[0].length; continue; }
    i += 1;
  }
  return tokens;
}

class GqlParser {
  private tokens: string[];
  private pos = 0;
  fragments = new Map<string, GqlSelection[]>();

  constructor(text: string) {
    this.tokens = tokenizeGql(text);
  }

  private peek(): string | undefined { return this.tokens[this.pos]; }
  private next(): string | undefined { const t = this.tokens[this.pos]; this.pos += 1; return t; }
  private expect(token: string): void { if (this.next() !== token) throw new Error(`expected ${token}`); }

  parseDocument(): GqlOp[] {
    const ops: GqlOp[] = [];
    while (this.pos < this.tokens.length) {
      const token = this.peek();
      if (token === 'query' || token === 'mutation' || token === 'subscription') {
        const opType = this.next() as string;
        let name: string | null = null;
        if (this.peek() !== '(' && this.peek() !== '{') name = this.next() ?? null;
        this.skipParens();
        this.skipDirectives();
        ops.push({ opType, name, selections: this.parseSelectionSet() });
      } else if (token === 'fragment') {
        this.next();
        const fragName = this.next() ?? '';
        if (this.peek() === 'on') { this.next(); this.next(); }
        this.skipDirectives();
        this.fragments.set(fragName, this.parseSelectionSet());
      } else if (token === '{') {
        ops.push({ opType: 'query', name: null, selections: this.parseSelectionSet() });
      } else {
        this.next();
      }
    }
    return ops;
  }

  private skipParens(): void {
    if (this.peek() !== '(') return;
    let depth = 0;
    do {
      const t = this.next();
      if (t === '(') depth += 1;
      else if (t === ')') depth -= 1;
    } while (depth > 0 && this.pos < this.tokens.length);
  }

  private skipDirectives(): void {
    while (this.peek() === '@') {
      this.next();
      this.next();
      this.skipParens();
    }
  }

  private parseSelectionSet(): GqlSelection[] {
    this.expect('{');
    const selections: GqlSelection[] = [];
    while (this.peek() !== '}' && this.pos < this.tokens.length) {
      if (this.peek() === '...') {
        this.next();
        if (this.peek() === 'on') {
          this.next();
          const typeName = this.next() ?? '';
          this.skipDirectives();
          selections.push({ kind: 'inline', typeName, selections: this.parseSelectionSet() });
        } else {
          selections.push({ kind: 'spread', name: this.next() ?? '' });
        }
        continue;
      }
      let name = this.next() ?? '';
      let alias: string | null = null;
      if (this.peek() === ':') {
        this.next();
        alias = name;
        name = this.next() ?? '';
      }
      const args = new Map<string, GqlValue>();
      if (this.peek() === '(') {
        this.next();
        while (this.peek() !== ')' && this.pos < this.tokens.length) {
          const argName = this.next() ?? '';
          this.expect(':');
          args.set(argName, this.parseValue());
        }
        this.expect(')');
      }
      this.skipDirectives();
      let sub: GqlSelection[] = [];
      if (this.peek() === '{') sub = this.parseSelectionSet();
      selections.push({ name, alias, args, selections: sub });
    }
    this.expect('}');
    return selections;
  }

  private parseValue(): GqlValue {
    const token = this.next() ?? '';
    if (token === '$') return { kind: 'var', name: this.next() ?? '' };
    if (token === '[') {
      const items: GqlValue[] = [];
      while (this.peek() !== ']' && this.pos < this.tokens.length) items.push(this.parseValue());
      this.expect(']');
      return { kind: 'list', items };
    }
    if (token === '{') {
      const fields = new Map<string, GqlValue>();
      while (this.peek() !== '}' && this.pos < this.tokens.length) {
        const key = this.next() ?? '';
        this.expect(':');
        fields.set(key, this.parseValue());
      }
      this.expect('}');
      return { kind: 'object', fields };
    }
    if (token.startsWith('"')) return { kind: 'scalar', value: token.slice(1, -1) };
    if (token === 'true') return { kind: 'scalar', value: true };
    if (token === 'false') return { kind: 'scalar', value: false };
    if (token === 'null') return { kind: 'scalar', value: null };
    if (/^-?\d+$/.test(token)) return { kind: 'scalar', value: parseInt(token, 10) };
    if (/^-?\d*\.\d+$/.test(token)) return { kind: 'scalar', value: parseFloat(token) };
    return { kind: 'scalar', value: token }; // enum literal
  }
}

function resolveGqlValue(value: GqlValue, variables: Record<string, unknown>): unknown {
  if (value.kind === 'var') return variables[value.name];
  if (value.kind === 'scalar') return value.value;
  if (value.kind === 'list') return value.items.map((item) => resolveGqlValue(item, variables));
  const out: Record<string, unknown> = {};
  for (const [key, entry] of value.fields) out[key] = resolveGqlValue(entry, variables);
  return out;
}

// The schema surface gh and github-mcp-server probe for.
const TYPE_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', 'nodes', '__type', '__schema', 'search', 'user', 'organization', 'rateLimit'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment', 'updateIssue', 'reopenIssue'],
  User: ['login', 'id', 'name', 'email', 'url', 'databaseId', 'repositories', 'issues', 'pullRequests'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'hasProjectsEnabled', 'hasWikiEnabled', 'issue', 'issues', 'pullRequest', 'pullRequests', 'description', 'isPrivate', 'url', 'htmlUrl', 'createdAt', 'updatedAt', 'refs', 'ref', 'isArchived', 'isFork', 'stargazerCount', 'forkCount', 'primaryLanguage', 'licenseInfo'],
  Issue: ['id', 'databaseId', 'number', 'title', 'state', 'body', 'bodyText', 'url', 'createdAt', 'updatedAt', 'closedAt', 'author', 'labels', 'comments', 'repository', 'closed', 'locked', 'activeLockReason', 'milestone', 'assignees', 'participants', 'reactions', 'timelineItems'],
  PullRequest: ['id', 'databaseId', 'number', 'title', 'body', 'bodyText', 'state', 'merged', 'mergedAt', 'mergeable', 'headRefName', 'baseRefName', 'headRef', 'baseRef', 'files', 'author', 'createdAt', 'updatedAt', 'closedAt', 'url', 'mergeCommit', 'additions', 'deletions', 'changedFiles', 'repository', 'closed', 'isDraft', 'labels', 'commits', 'reviews', 'comments'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  IssueEdge: ['node', 'cursor'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestEdge: ['node', 'cursor'],
  PullRequestChangedFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestChangedFile: ['path', 'additions', 'deletions', 'changeType', 'viewerViewedState'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'],
  Ref: ['name', 'prefix', 'target', 'associatedPullRequests', 'repository'],
  Commit: ['id', 'oid', 'message', 'messageHeadline', 'authoredDate', 'author', 'tree', 'url'],
  IssueComment: ['id', 'databaseId', 'body', 'bodyText', 'createdAt', 'updatedAt', 'author', 'url', 'issue'],
  Label: ['id', 'name', 'color', 'description', 'url'],
  LabelConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  CommentEdge: ['node', 'cursor'],
  CreateIssuePayload: ['clientMutationId', 'issue'],
  CloseIssuePayload: ['clientMutationId', 'issue'],
  CreatePullRequestPayload: ['clientMutationId', 'pullRequest'],
  MergePullRequestPayload: ['clientMutationId', 'pullRequest'],
  AddCommentPayload: ['clientMutationId', 'commentEdge', 'subject'],
  __Type: ['name', 'kind', 'description', 'fields', 'enumValues', 'possibleTypes', 'inputFields', 'ofType', 'specifiedByURL'],
  __Field: ['name', 'description', 'args', 'type', 'isDeprecated', 'deprecationReason'],
  __EnumValue: ['name', 'description', 'isDeprecated', 'deprecationReason'],
  __InputValue: ['name', 'description', 'type', 'defaultValue'],
  __Schema: ['description', 'types', 'queryType', 'mutationType', 'subscriptionType', 'directives'],
  __Directive: ['name', 'description', 'locations', 'args'],
  Node: ['id'],
  SearchResultItemConnection: ['nodes', 'edges', 'pageInfo', 'issueCount'],
};

const ENUM_VALUES: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  OrderDirection: ['ASC', 'DESC'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
};

interface GqlCtx {
  variables: Record<string, unknown>;
  errors: Array<{ message: string }>;
  fragments: Map<string, GqlSelection[]>;
}

type GqlSource = Record<string, unknown> & { __type: string };

function wrapRepo(repo: RepoRec): GqlSource { return { __type: 'Repository', repo } as GqlSource; }
function wrapIssue(repo: RepoRec, issue: IssueRec): GqlSource { return { __type: 'Issue', repo, issue } as GqlSource; }
function wrapPull(repo: RepoRec, pull: PullRec): GqlSource { return { __type: 'PullRequest', repo, pull } as GqlSource; }

function issueGqlState(issue: IssueRec): string { return issue.state === 'open' ? 'OPEN' : 'CLOSED'; }
function pullGqlState(pull: PullRec): string { return pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED'; }

function cursorOf(index: number): string {
  return Buffer.from(`cursor:${index}`, 'utf8').toString('base64');
}

function offsetOf(cursor: unknown): number {
  if (typeof cursor !== 'string' || cursor === '') return 0;
  try {
    const text = Buffer.from(cursor, 'base64').toString('utf8');
    const match = /^cursor:(\d+)$/.exec(text);
    return match ? parseInt(match[1] as string, 10) : 0;
  } catch {
    return 0;
  }
}

function childType(parentType: string, field: string): string {
  const map: Record<string, string> = {
    'Query.viewer': 'User', 'Query.repository': 'Repository', 'Query.node': 'Node', 'Query.__type': '__Type', 'Query.__schema': '__Schema', 'Query.user': 'User',
    'Repository.owner': 'User', 'Repository.defaultBranchRef': 'Ref', 'Repository.issue': 'Issue', 'Repository.issues': 'IssueConnection',
    'Repository.pullRequest': 'PullRequest', 'Repository.pullRequests': 'PullRequestConnection',
    'IssueConnection.nodes': 'Issue', 'IssueConnection.pageInfo': 'PageInfo', 'IssueConnection.edges': 'IssueEdge',
    'IssueEdge.node': 'Issue',
    'PullRequestConnection.nodes': 'PullRequest', 'PullRequestConnection.pageInfo': 'PageInfo', 'PullRequestConnection.edges': 'PullRequestEdge',
    'PullRequestEdge.node': 'PullRequest',
    'PullRequest.files': 'PullRequestChangedFileConnection',
    'PullRequestChangedFileConnection.nodes': 'PullRequestChangedFile', 'PullRequestChangedFileConnection.pageInfo': 'PageInfo',
    'PullRequest.headRef': 'Ref', 'PullRequest.baseRef': 'Ref', 'PullRequest.repository': 'Repository', 'PullRequest.author': 'User',
    'Issue.author': 'User', 'Issue.repository': 'Repository', 'Issue.labels': 'LabelConnection',
    'LabelConnection.nodes': 'Label',
    'CreateIssuePayload.issue': 'Issue', 'CloseIssuePayload.issue': 'Issue',
    'CreatePullRequestPayload.pullRequest': 'PullRequest', 'MergePullRequestPayload.pullRequest': 'PullRequest',
    'AddCommentPayload.commentEdge': 'CommentEdge', 'AddCommentPayload.subject': 'Issue',
    'CommentEdge.node': 'IssueComment',
    '__Type.fields': '__Field', '__Type.enumValues': '__EnumValue', '__Type.ofType': '__Type',
    '__Field.type': '__Type', '__Field.args': '__InputValue',
  };
  return map[`${parentType}.${field}`] ?? 'JSON';
}

async function resolveGqlField(typeName: string, source: GqlSource | null, field: string, args: Map<string, GqlValue>, ctx: GqlCtx): Promise<unknown> {
  const arg = (name: string): unknown => {
    const value = args.get(name);
    return value ? resolveGqlValue(value, ctx.variables) : undefined;
  };

  if (field === '__type' && (typeName === 'Query' || typeName === '')) {
    const name = String(arg('name') ?? '');
    return { __type: '__Type', typeName: name };
  }
  if (field === '__schema') return { __type: '__Schema' };

  if (typeName === '__Type' && source) {
    const typeName2 = String(source.typeName ?? '');
    if (field === 'name') return typeName2;
    if (field === 'kind') return ENUM_VALUES[typeName2] ? 'ENUM' : 'OBJECT';
    if (field === 'description') return null;
    if (field === 'fields') return (TYPE_FIELDS[typeName2] ?? []).map((name) => ({ __type: '__Field', name }));
    if (field === 'enumValues') return (ENUM_VALUES[typeName2] ?? []).map((name) => ({ __type: '__EnumValue', name }));
    if (field === 'possibleTypes' || field === 'inputFields') return [];
    if (field === 'ofType') return null;
    return null;
  }
  if (typeName === '__Field' && source) {
    if (field === 'name') return source.name;
    if (field === 'description') return null;
    if (field === 'isDeprecated') return false;
    if (field === 'deprecationReason') return null;
    if (field === 'args') return [];
    if (field === 'type') return { __type: '__Type', typeName: 'String' };
    return null;
  }
  if (typeName === '__EnumValue' && source) {
    if (field === 'name') return source.name;
    if (field === 'description') return null;
    if (field === 'isDeprecated') return false;
    return null;
  }
  if (typeName === '__Schema') {
    if (field === 'queryType') return { __type: '__Type', typeName: 'Query' };
    if (field === 'mutationType') return { __type: '__Type', typeName: 'Mutation' };
    if (field === 'types') return Object.keys(TYPE_FIELDS).map((typeName) => ({ __type: '__Type', typeName }));
    return null;
  }

  if (typeName === 'Query' || typeName === '') {
    if (field === 'viewer') return { __type: 'User', login: OWNER };
    if (field === 'user') return { __type: 'User', login: String(arg('login') ?? OWNER) };
    if (field === 'repository') {
      const owner = String(arg('owner') ?? '');
      const name = String(arg('name') ?? '');
      const actor = forge.actor(owner, name);
      if (!actor) return null;
      return wrapRepo(actor.repo);
    }
    if (field === 'node') {
      const parsed = parseGlobalId(String(arg('id') ?? ''));
      if (!parsed) return null;
      if (parsed.kind === 'Repository') {
        const actor = forge.findById(parseInt(parsed.payload, 10));
        return actor ? wrapRepo(actor.repo) : null;
      }
      if (parsed.kind === 'Issue' || parsed.kind === 'PullRequest') {
        const [repoIdRaw, numberRaw] = parsed.payload.split(':');
        const actor = forge.findById(parseInt(repoIdRaw ?? '', 10));
        if (!actor) return null;
        const number = parseInt(numberRaw ?? '', 10);
        if (parsed.kind === 'Issue') {
          const issue = actor.repo.issues.get(number);
          return issue ? wrapIssue(actor.repo, issue) : null;
        }
        const pull = actor.repo.pulls.get(number);
        return pull ? wrapPull(actor.repo, pull) : null;
      }
      return null;
    }
    return null;
  }

  if (typeName === 'User' && source) {
    if (field === 'login') return source.login ?? OWNER;
    if (field === 'id') return globalId('User', String(OWNER_ID));
    if (field === 'databaseId') return OWNER_ID;
    if (field === 'name') return OWNER_NAME;
    if (field === 'email') return OWNER_EMAIL;
    if (field === 'url') return `/${String(source.login ?? OWNER)}`;
    return null;
  }

  if (typeName === 'Repository' && source) {
    const repo = source.repo as RepoRec;
    switch (field) {
      case 'id': return globalId('Repository', String(repo.id));
      case 'databaseId': return repo.id;
      case 'name': return repo.name;
      case 'nameWithOwner': return `${repo.owner}/${repo.name}`;
      case 'owner': return { __type: 'User', login: repo.owner };
      case 'defaultBranchRef': return { __type: 'Ref', name: repo.defaultBranch, repo };
      case 'viewerPermission': return 'ADMIN';
      case 'hasIssuesEnabled': return true;
      case 'hasProjectsEnabled': return true;
      case 'hasWikiEnabled': return true;
      case 'description': return repo.description;
      case 'isPrivate': return repo.isPrivate;
      case 'isArchived': return false;
      case 'isFork': return false;
      case 'url': case 'htmlUrl': return `/${repo.owner}/${repo.name}`;
      case 'createdAt': return isoAt(repo.id);
      case 'updatedAt': return isoAt(repo.id + repo.seq);
      case 'stargazerCount': case 'forkCount': return 0;
      case 'issue': {
        const issue = repo.issues.get(Number(arg('number')));
        return issue ? wrapIssue(repo, issue) : null;
      }
      case 'issues': {
        let list = [...repo.issues.values()];
        const states = arg('states');
        if (Array.isArray(states) && states.length > 0) {
          const wanted = states.map((s) => String(s).toLowerCase());
          list = list.filter((i) => wanted.includes(i.state));
        }
        const orderBy = arg('orderBy') as Record<string, unknown> | undefined;
        const descending = orderBy && String(orderBy.direction ?? '') === 'DESC';
        list.sort((a, b) => (descending ? b.number - a.number : a.number - b.number));
        const first = typeof arg('first') === 'number' ? (arg('first') as number) : 100;
        const offset = offsetOf(arg('after'));
        const page = list.slice(offset, offset + first);
        return {
          __type: 'IssueConnection', nodes: page.map((i) => wrapIssue(repo, i)),
          totalCount: list.length, hasNextPage: offset + page.length < list.length,
          endCursor: page.length > 0 ? cursorOf(offset + page.length) : null,
          edges: page.map((i, idx) => ({ __type: 'IssueEdge', node: wrapIssue(repo, i), cursor: cursorOf(offset + idx + 1) })),
        };
      }
      case 'pullRequest': {
        const pull = repo.pulls.get(Number(arg('number')));
        return pull ? wrapPull(repo, pull) : null;
      }
      case 'pullRequests': {
        let list = [...repo.pulls.values()];
        const states = arg('states');
        if (Array.isArray(states) && states.length > 0) {
          const wanted = states.map((s) => String(s));
          list = list.filter((p) => wanted.includes(pullGqlState(p)));
        }
        list.sort((a, b) => b.number - a.number);
        const first = typeof arg('first') === 'number' ? (arg('first') as number) : 100;
        const offset = offsetOf(arg('after'));
        const page = list.slice(offset, offset + first);
        return {
          __type: 'PullRequestConnection', nodes: page.map((p) => wrapPull(repo, p)),
          totalCount: list.length, hasNextPage: offset + page.length < list.length,
          endCursor: page.length > 0 ? cursorOf(offset + page.length) : null,
          edges: page.map((p, idx) => ({ __type: 'PullRequestEdge', node: wrapPull(repo, p), cursor: cursorOf(offset + idx + 1) })),
        };
      }
      default: return null;
    }
  }

  if (typeName === 'Ref' && source) {
    if (field === 'name') return source.name;
    if (field === 'prefix') return 'refs/heads/';
    if (field === 'target') {
      const repo = source.repo as RepoRec | undefined;
      const sha = repo ? tipOf(repo, String(source.name)) : null;
      return sha ? { __type: 'Commit', oid: sha } : null;
    }
    if (field === 'repository') return source.repo ? wrapRepo(source.repo as RepoRec) : null;
    return null;
  }
  if (typeName === 'Commit' && source) {
    if (field === 'oid' || field === 'id') return source.oid;
    if (field === 'message') {
      const obj = getObject(String(source.oid));
      return obj ? parseCommit(obj.data).message : '';
    }
    return null;
  }

  if (typeName === 'Issue' && source) {
    const repo = source.repo as RepoRec;
    const issue = source.issue as IssueRec;
    switch (field) {
      case 'id': return globalId('Issue', `${repo.id}:${issue.number}`);
      case 'databaseId': return repo.id * 100000 + issue.number;
      case 'number': return issue.number;
      case 'title': return issue.title;
      case 'body': case 'bodyText': return issue.body;
      case 'state': return issueGqlState(issue);
      case 'closed': return issue.state === 'closed';
      case 'locked': return false;
      case 'url': return `/${repo.owner}/${repo.name}/issues/${issue.number}`;
      case 'createdAt': return isoAt(issue.seq);
      case 'updatedAt': return isoAt(issue.seq);
      case 'closedAt': return issue.state === 'closed' ? isoAt(issue.seq + 1) : null;
      case 'author': return { __type: 'User', login: OWNER };
      case 'repository': return wrapRepo(repo);
      case 'labels': return { __type: 'LabelConnection', nodes: issue.labels.map((name) => ({ __type: 'Label', name, color: repo.labels.get(name)?.color ?? 'ededed' })) };
      case 'comments': return { __type: 'IssueCommentConnection', nodes: issue.comments.map((c) => ({ __type: 'IssueComment', idNum: c.id, body: c.body, repo, issue })) };
      default: return null;
    }
  }

  if (typeName === 'PullRequest' && source) {
    const repo = source.repo as RepoRec;
    const pull = source.pull as PullRec;
    switch (field) {
      case 'id': return globalId('PullRequest', `${repo.id}:${pull.number}`);
      case 'databaseId': return repo.id * 100000 + pull.number;
      case 'number': return pull.number;
      case 'title': return pull.title;
      case 'body': case 'bodyText': return pull.body;
      case 'state': return pullGqlState(pull);
      case 'merged': return pull.merged;
      case 'mergedAt': return pull.mergedAt;
      case 'closed': return pull.state === 'closed';
      case 'isDraft': return false;
      case 'mergeable': return pull.state !== 'open' ? 'UNKNOWN' : pullConflicted(repo, pull) ? 'CONFLICTING' : 'MERGEABLE';
      case 'headRefName': return pull.head;
      case 'baseRefName': return pull.base;
      case 'headRef': return { __type: 'Ref', name: pull.head, repo };
      case 'baseRef': return { __type: 'Ref', name: pull.base, repo };
      case 'author': return { __type: 'User', login: OWNER };
      case 'repository': return wrapRepo(repo);
      case 'createdAt': return isoAt(pull.seq);
      case 'updatedAt': return isoAt(pull.seq);
      case 'closedAt': return pull.state === 'closed' ? pull.mergedAt ?? isoAt(pull.seq + 1) : null;
      case 'url': return `/${repo.owner}/${repo.name}/pull/${pull.number}`;
      case 'mergeCommit': return pull.mergeCommitSha ? { __type: 'Commit', oid: pull.mergeCommitSha } : null;
      case 'files': {
        const headTip = repo.refs.get(branchRef(pull.head)) ?? pull.headSha;
        const baseTip = tipOf(repo, pull.base);
        const origin = baseTip ? mergeBase(baseTip, headTip) : null;
        const files = diffFiles(origin, headTip);
        const first = typeof arg('first') === 'number' ? (arg('first') as number) : 100;
        return {
          __type: 'PullRequestChangedFileConnection',
          nodes: files.slice(0, first).map((f) => ({ __type: 'PullRequestChangedFile', path: f.filename, additions: f.additions, deletions: f.deletions, changeType: f.status === 'added' ? 'ADDED' : f.status === 'removed' ? 'DELETED' : 'MODIFIED' })),
          totalCount: files.length, hasNextPage: false, endCursor: null, edges: [],
        };
      }
      case 'additions': case 'deletions': case 'changedFiles': {
        const headTip = repo.refs.get(branchRef(pull.head)) ?? pull.headSha;
        const baseTip = tipOf(repo, pull.base);
        const origin = baseTip ? mergeBase(baseTip, headTip) : null;
        const files = diffFiles(origin, headTip);
        if (field === 'changedFiles') return files.length;
        return files.reduce((sum, f) => sum + (field === 'additions' ? f.additions : f.deletions), 0);
      }
      default: return null;
    }
  }

  if ((typeName === 'IssueConnection' || typeName === 'PullRequestConnection' || typeName === 'LabelConnection') && source) {
    if (field === 'nodes') return source.nodes;
    if (field === 'edges') return source.edges ?? [];
    if (field === 'totalCount') return source.totalCount ?? (Array.isArray(source.nodes) ? source.nodes.length : 0);
    if (field === 'pageInfo') {
      return { __type: 'PageInfo', hasNextPage: source.hasNextPage ?? false, hasPreviousPage: false, startCursor: null, endCursor: source.endCursor ?? null };
    }
    return null;
  }
  if ((typeName === 'IssueEdge' || typeName === 'PullRequestEdge' || typeName === 'CommentEdge') && source) {
    if (field === 'node') return source.node;
    if (field === 'cursor') return source.cursor;
    return null;
  }
  if (typeName === 'PageInfo' && source) {
    if (field === 'hasNextPage') return source.hasNextPage ?? false;
    if (field === 'hasPreviousPage') return false;
    if (field === 'endCursor') return source.endCursor ?? null;
    if (field === 'startCursor') return source.startCursor ?? null;
    return null;
  }
  if (typeName === 'PullRequestChangedFileConnection' && source) {
    if (field === 'nodes') return source.nodes;
    if (field === 'totalCount') return source.totalCount ?? 0;
    if (field === 'pageInfo') return { __type: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null };
    if (field === 'edges') return [];
    return null;
  }
  if (typeName === 'PullRequestChangedFile' && source) {
    if (field === 'path') return source.path;
    if (field === 'additions') return source.additions;
    if (field === 'deletions') return source.deletions;
    if (field === 'changeType') return source.changeType;
    return null;
  }
  if (typeName === 'IssueComment' && source) {
    if (field === 'id') return globalId('IssueComment', `${(source.repo as RepoRec).id}:${(source.issue as IssueRec).number}:${source.idNum}`);
    if (field === 'body' || field === 'bodyText') return source.body;
    if (field === 'author') return { __type: 'User', login: OWNER };
    if (field === 'createdAt') return isoAt(Number(source.idNum ?? 0));
    return null;
  }
  if (typeName === 'Label' && source) {
    if (field === 'name') return source.name;
    if (field === 'color') return source.color;
    if (field === 'id') return globalId('Label', String(source.name));
    return null;
  }

  if (typeName === 'Mutation') {
    const input = (arg('input') ?? {}) as Record<string, unknown>;
    if (field === 'createIssue') {
      const parsed = parseGlobalId(String(input.repositoryId ?? ''));
      const actor = parsed && parsed.kind === 'Repository' ? forge.findById(parseInt(parsed.payload, 10)) : null;
      if (!actor) { ctx.errors.push({ message: 'Repository not found for createIssue' }); return null; }
      const created = await actor.post((repo) => {
        commitSeq += 1;
        const issue: IssueRec = {
          number: repo.nextNumber, title: String(input.title ?? ''), body: String(input.body ?? ''),
          state: 'open', labels: [], seq: commitSeq, comments: [],
        };
        repo.nextNumber += 1;
        repo.issues.set(issue.number, issue);
        return wrapIssue(repo, issue);
      });
      return { __type: 'CreateIssuePayload', issue: created, clientMutationId: input.clientMutationId ?? null };
    }
    if (field === 'closeIssue') {
      const parsed = parseGlobalId(String(input.issueId ?? ''));
      if (!parsed) return null;
      const [repoIdRaw, numberRaw] = parsed.payload.split(':');
      const actor = forge.findById(parseInt(repoIdRaw ?? '', 10));
      if (!actor) return null;
      const number = parseInt(numberRaw ?? '', 10);
      const closed = await actor.post((repo) => {
        const issue = repo.issues.get(number);
        if (!issue) return null;
        issue.state = 'closed';
        return wrapIssue(repo, issue);
      });
      return { __type: 'CloseIssuePayload', issue: closed, clientMutationId: input.clientMutationId ?? null };
    }
    if (field === 'createPullRequest') {
      const parsed = parseGlobalId(String(input.repositoryId ?? ''));
      const actor = parsed && parsed.kind === 'Repository' ? forge.findById(parseInt(parsed.payload, 10)) : null;
      if (!actor) { ctx.errors.push({ message: 'Repository not found for createPullRequest' }); return null; }
      const created = await actor.post((repo) => {
        const head = String(input.headRefName ?? '');
        const base = String(input.baseRefName ?? '') || repo.defaultBranch;
        for (const existing of repo.pulls.values()) {
          if (existing.state === 'open' && existing.head === head && existing.base === base) return wrapPull(repo, existing);
        }
        const headTip = repo.refs.get(branchRef(head));
        if (!headTip) return null;
        commitSeq += 1;
        const pull: PullRec = {
          number: repo.nextNumber, title: String(input.title ?? ''), body: String(input.body ?? ''),
          head, base, headSha: headTip, state: 'open', merged: false, mergedAt: null, mergeCommitSha: null, seq: commitSeq,
        };
        repo.nextNumber += 1;
        repo.pulls.set(pull.number, pull);
        return wrapPull(repo, pull);
      });
      if (!created) { ctx.errors.push({ message: 'Head branch not found for createPullRequest' }); return null; }
      return { __type: 'CreatePullRequestPayload', pullRequest: created, clientMutationId: input.clientMutationId ?? null };
    }
    if (field === 'mergePullRequest') {
      const parsed = parseGlobalId(String(input.pullRequestId ?? ''));
      if (!parsed) return null;
      const [repoIdRaw, numberRaw] = parsed.payload.split(':');
      const actor = forge.findById(parseInt(repoIdRaw ?? '', 10));
      if (!actor) return null;
      const number = parseInt(numberRaw ?? '', 10);
      const merged = await actor.post((repo) => {
        const pull = repo.pulls.get(number);
        if (!pull) return null;
        if (!pull.merged) mergePull(repo, pull);
        return wrapPull(repo, pull);
      });
      return { __type: 'MergePullRequestPayload', pullRequest: merged, clientMutationId: input.clientMutationId ?? null };
    }
    if (field === 'addComment') {
      const parsed = parseGlobalId(String(input.subjectId ?? ''));
      if (!parsed) return null;
      const [repoIdRaw, numberRaw] = parsed.payload.split(':');
      const actor = forge.findById(parseInt(repoIdRaw ?? '', 10));
      if (!actor) return null;
      const number = parseInt(numberRaw ?? '', 10);
      const edge = await actor.post((repo) => {
        const issue = repo.issues.get(number);
        if (!issue) return null;
        commentSeq += 1;
        const comment = { id: commentSeq, body: String(input.body ?? '') };
        issue.comments.push(comment);
        return { __type: 'CommentEdge', node: { __type: 'IssueComment', idNum: comment.id, body: comment.body, repo, issue }, cursor: cursorOf(comment.id) };
      });
      return { __type: 'AddCommentPayload', commentEdge: edge, clientMutationId: input.clientMutationId ?? null };
    }
    return null;
  }

  // Payload wrappers and any remaining object types: read the stored property.
  if (source && field in source) return source[field];
  return null;
}

async function executeSelections(typeName: string, source: GqlSource | null, selections: GqlSelection[], ctx: GqlCtx): Promise<Record<string, unknown>> {
  const out: Record<string, unknown> = {};
  for (const selection of selections) {
    if ('kind' in selection && selection.kind === 'inline') {
      const actual = source?.__type ?? typeName;
      if (selection.typeName === actual || selection.typeName === 'Node' || actual === 'Node') {
        const merged = await executeSelections(selection.typeName, source, selection.selections, ctx);
        Object.assign(out, merged);
      }
      continue;
    }
    if ('kind' in selection && selection.kind === 'spread') {
      const frag = ctx.fragments.get(selection.name);
      if (frag) Object.assign(out, await executeSelections(typeName, source, frag, ctx));
      continue;
    }
    const field = selection as GqlField;
    const key = field.alias ?? field.name;
    const known = TYPE_FIELDS[typeName];
    if (known && !known.includes(field.name) && field.name !== '__typename') {
      ctx.errors.push({ message: `Field '${field.name}' doesn't exist on type '${typeName}'` });
      out[key] = null;
      continue;
    }
    if (field.name === '__typename') { out[key] = source?.__type ?? typeName; continue; }
    const value = await resolveGqlField(typeName, source, field.name, field.args, ctx);
    if (field.selections.length === 0 || value === null || value === undefined) {
      out[key] = value ?? null;
      continue;
    }
    const child = childType(typeName, field.name);
    if (Array.isArray(value)) {
      const items: unknown[] = [];
      for (const item of value) {
        items.push(typeof item === 'object' && item !== null ? await executeSelections(child, item as GqlSource, field.selections, ctx) : item);
      }
      out[key] = items;
    } else if (typeof value === 'object') {
      const src = value as GqlSource;
      const effective = typeof src.__type === 'string' && src.__type !== '' ? src.__type : child;
      out[key] = await executeSelections(effective, src, field.selections, ctx);
    } else {
      out[key] = value;
    }
  }
  return out;
}

async function executeGraphql(body: unknown): Promise<Reply> {
  if (Array.isArray(body)) {
    const results: unknown[] = [];
    for (const entry of body) results.push((await executeGraphql(entry)).body);
    return { status: 200, body: results };
  }
  const record = asRecord(body);
  const query = typeof record.query === 'string' ? record.query : '';
  const variables = asRecord(record.variables) as Record<string, unknown>;
  if (query === '') return { status: 400, body: { errors: [{ message: 'No query provided' }] } };
  let ops: GqlOp[];
  let fragments: Map<string, GqlSelection[]>;
  try {
    const parser = new GqlParser(query);
    ops = parser.parseDocument();
    fragments = parser.fragments;
  } catch (err) {
    return { status: 200, body: { errors: [{ message: err instanceof Error ? err.message : 'Parse error' }] } };
  }
  const ctx: GqlCtx = { variables, errors: [], fragments };
  const data: Record<string, unknown> = {};
  for (const op of ops) {
    const rootType = op.opType === 'mutation' ? 'Mutation' : 'Query';
    const part = await executeSelections(rootType, { __type: rootType }, op.selections, ctx);
    Object.assign(data, part);
  }
  const replyBody: Record<string, unknown> = { data };
  if (ctx.errors.length > 0) replyBody.errors = ctx.errors;
  return { status: 200, body: replyBody };
}

// --------------------------------------------------------------------------- MCP

const MCP_SERVER_INFO = { name: 'sage-owl-forge', version: VERSION };
const MCP_VERSIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];

const MCP_TOOLS: Array<Record<string, unknown>> = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The repository name.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository, optionally filtered by state.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'Issue state filter: open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
        body: { type: 'string', description: 'The pull request body.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request by number (squash merge).',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'number', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

const MCP_REQUIRED: Record<string, string[]> = {
  create_repo: ['name'],
  get_repo: ['owner', 'repo'],
  create_issue: ['owner', 'repo', 'title'],
  list_issues: ['owner', 'repo'],
  create_pull_request: ['owner', 'repo', 'title', 'head', 'base'],
  merge_pull_request: ['owner', 'repo', 'pull_number'],
};

function toolResult(data: unknown, isError = false): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: typeof data === 'string' ? data : JSON.stringify(data) }],
    structuredContent: typeof data === 'string' ? { message: data } : data,
    isError,
  };
}

async function callMcpTool(name: string, args: Json): Promise<Record<string, unknown>> {
  const required = MCP_REQUIRED[name];
  if (!required) {
    return { __rpcError: { code: -32602, message: `Unknown tool: ${name}` } };
  }
  for (const key of required) {
    if (args[key] === undefined || args[key] === null || args[key] === '') {
      return toolResult(`Missing required argument: ${key}`, true);
    }
  }
  const owner = str(args.owner) || OWNER;
  const repoName = str(args.repo);

  if (name === 'create_repo') {
    const repoNameNew = str(args.name);
    const existing = forge.actor(OWNER, repoNameNew);
    if (existing) return toolResult(repoJson(existing.repo));
    const created = forge.createRepo(repoNameNew, str(args.description), args.private === true, 'main');
    if (!created) return toolResult('Repository already exists', true);
    return toolResult(repoJson(created));
  }

  const actor = forge.actor(owner, repoName);
  if (!actor) return toolResult(`Repository ${owner}/${repoName} not found`, true);

  if (name === 'get_repo') {
    return actor.post((repo) => toolResult(repoJson(repo)));
  }
  if (name === 'create_issue') {
    return actor.post((repo) => {
      const reply = createIssueReply(repo, { title: args.title, body: args.body ?? '' });
      if (reply.status !== 201) return toolResult((reply.body as Json)?.message ?? 'Could not create issue', true);
      return toolResult(reply.body);
    });
  }
  if (name === 'list_issues') {
    return actor.post((repo) => {
      const state = str(args.state) || 'open';
      let list = [...repo.issues.values()];
      if (state === 'open') list = list.filter((i) => i.state === 'open');
      else if (state === 'closed') list = list.filter((i) => i.state === 'closed');
      list.sort((a, b) => a.number - b.number);
      return toolResult(list.map((i) => issueJson(repo, i)));
    });
  }
  if (name === 'create_pull_request') {
    return actor.post((repo) => {
      const reply = createPullReply(repo, { title: args.title, body: args.body ?? '', head: args.head, base: args.base });
      if (reply.status !== 201) return toolResult((reply.body as Json)?.message ?? 'Could not create pull request', true);
      return toolResult(reply.body);
    });
  }
  // merge_pull_request
  return actor.post((repo) => {
    const pull = repo.pulls.get(Number(args.pull_number));
    if (!pull) return toolResult('Pull request not found', true);
    if (!pull.merged) {
      const sha = mergePull(repo, pull);
      if (!sha) return toolResult('Pull request is not mergeable: conflict', true);
    }
    return toolResult(pullJson(repo, pull));
  });
}

async function processMcp(message: Json): Promise<Reply | null> {
  const method = str(message.method);
  const id = message.id;
  const params = asRecord(message.params);
  if (id === undefined || id === null) {
    return { status: 202, empty: true }; // a notification: accepted, nothing to answer
  }
  const ok = (result: unknown): Reply => ({ status: 200, body: { jsonrpc: '2.0', id, result } });
  const failWith = (code: number, text: string): Reply => ({ status: 200, body: { jsonrpc: '2.0', id, error: { code, message: text } } });

  if (method === 'server/discover') {
    return ok({
      resultType: 'complete',
      supportedVersions: MCP_VERSIONS,
      capabilities: { tools: {} },
      serverInfo: MCP_SERVER_INFO,
      _meta: { 'io.modelcontextprotocol/serverInfo': MCP_SERVER_INFO },
    });
  }
  if (method === 'initialize') {
    const requested = str(params.protocolVersion);
    const chosen = MCP_VERSIONS.includes(requested) ? requested : '2025-11-25';
    return ok({ protocolVersion: chosen, capabilities: { tools: {} }, serverInfo: MCP_SERVER_INFO });
  }
  if (method === 'ping') return ok({});
  if (method === 'tools/list') return ok({ tools: MCP_TOOLS });
  if (method === 'tools/call') {
    const toolName = str(params.name);
    const args = asRecord(params.arguments);
    const result = await callMcpTool(toolName, args);
    if (typeof result === 'object' && result !== null && '__rpcError' in result) {
      const rpcError = (result as { __rpcError: { code: number; message: string } }).__rpcError;
      return failWith(rpcError.code, rpcError.message);
    }
    return ok(result);
  }
  return failWith(-32601, `Method not found: ${method}`);
}

async function handleMcp(bodyText: string): Promise<Reply> {
  let parsed: unknown;
  try {
    parsed = JSON.parse(bodyText);
  } catch {
    return { status: 400, body: { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } } };
  }
  if (Array.isArray(parsed)) {
    const replies: unknown[] = [];
    for (const entry of parsed) {
      const reply = await processMcp(asRecord(entry));
      if (reply && !reply.empty) replies.push(reply.body);
    }
    return { status: 200, body: replies };
  }
  const reply = await processMcp(asRecord(parsed));
  return reply ?? { status: 202, empty: true };
}

// --------------------------------------------------------------------------- the server

export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async () => {
      try {
        const url = new URL(req.url ?? '/', 'http://entry');
        const rawSegments = url.pathname.split('/').filter((s) => s !== '');
        const segments = rawSegments.map((s) => {
          try { return decodeURIComponent(s); } catch { return s; }
        });
        const method = req.method ?? 'GET';

        if (method === 'GET' && url.pathname === '/healthz') {
          sendJson(res, { status: 200, body: { ok: true } });
          return;
        }

        const bodyBuffer = await readBody(req);
        const bodyText = bodyBuffer.toString('utf8');

        if (!authed(req)) {
          sendJson(res, errReply(401, 'Unauthorized'));
          return;
        }

        if (segments[0] === 'api' && segments[1] === 'v3') {
          sendJson(res, await handleRest(req, url, segments.slice(2), bodyText));
          return;
        }

        if (url.pathname === '/api/graphql') {
          if (method !== 'POST') { sendJson(res, notFound()); return; }
          let parsedBody: unknown;
          try {
            parsedBody = JSON.parse(bodyText);
          } catch {
            sendJson(res, { status: 400, body: { errors: [{ message: 'Malformed JSON body' }] } });
            return;
          }
          sendJson(res, await executeGraphql(parsedBody));
          return;
        }

        if (url.pathname === '/mcp') {
          if (method !== 'POST') {
            sendJson(res, { status: 405, body: { jsonrpc: '2.0', id: null, error: { code: -32601, message: 'Method not allowed' } } });
            return;
          }
          sendJson(res, await handleMcp(bodyText));
          return;
        }

        if (segments.length >= 3 && (segments[1] ?? '').endsWith('.git')) {
          await handleGit(req, res, segments[0] ?? '', segments[1] ?? '', segments.slice(2).join('/'), url, bodyBuffer);
          return;
        }

        sendJson(res, notFound());
      } catch (err) {
        try {
          sendJson(res, errReply(500, err instanceof Error ? err.message : 'Internal error'));
        } catch {
          // the socket is already gone; nothing more to say
        }
      }
    })();
  });
}
