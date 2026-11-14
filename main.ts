// Entry point: the lifecycle this process owes the trial environment.
//
// The forge itself lives in app.ts. This file only performs the handshake around it:
//   1. read the environment origin from MAKEFUN_ENV_URL (without it there is nobody to serve);
//   2. start the forge on an ephemeral port — listen(0), never a fixed port;
//   3. POST {"port": N} to the environment's /register so it can dial back;
//   4. poll GET /done, with a short backoff between attempts, until the environment
//      answers {"done": true};
//   5. close the server and exit 0.
// Register answers 409 when another process registered first; that is not ours to
// fix, so we accept it and keep waiting. Other failures are retried, because the
// environment may still be starting when we first call it.

import { createApp } from './app.ts';

const envUrl = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
if (envUrl === '') {
  process.stderr.write('[sage-owl] MAKEFUN_ENV_URL is not set; exiting\n');
  process.exit(1);
}

const TIMEOUT_MS = 30000;

function wait(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function backoff(attempt: number): number {
  return Math.min(2000, 250 * 2 ** Math.min(attempt, 8));
}

async function announce(port: number): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    try {
      const res = await fetch(`${envUrl}/register`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(TIMEOUT_MS),
      });
      if (res.status === 200 || res.status === 409) return;
      if (res.status === 400 || res.status === 405) {
        throw new Error(`register refused with HTTP ${res.status}`);
      }
    } catch (err) {
      if (err instanceof Error && err.message.startsWith('register refused')) throw err;
    }
    await wait(backoff(attempt));
  }
}

async function waitUntilDone(): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    try {
      const res = await fetch(`${envUrl}/done`, { signal: AbortSignal.timeout(TIMEOUT_MS) });
      if (res.ok) {
        const body = (await res.json()) as { done?: unknown };
        if (body.done === true) return;
      }
    } catch {
      // Not answered yet is not "done"; keep polling.
    }
    await wait(backoff(attempt));
  }
}

async function run(): Promise<void> {
  const server = createApp();
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, () => resolve());
  });
  const address = server.address();
  if (address === null || typeof address === 'string') throw new Error('no ephemeral port was bound');
  process.stdout.write(`[sage-owl] forge listening on ${address.port}\n`);
  await announce(address.port);
  process.stdout.write('[sage-owl] registered; serving until the environment says done\n');
  await waitUntilDone();
  server.close();
  process.stdout.write('[sage-owl] done\n');
}

try {
  await run();
  process.exit(0);
} catch (err) {
  process.stderr.write(`[sage-owl] ${err instanceof Error ? err.message : String(err)}\n`);
  process.exit(1);
}
