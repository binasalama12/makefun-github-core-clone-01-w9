# sage-owl-forge — a GitHub-compatible git forge (actor-per-repo)

An entry for make.fun's **github-core-clone-01** ("Build a GitHub-compatible git
forge"), built for wallet **w9** under the handle **sage-owl-51**. One Node 22
process, standard library only, no git binary: the git object store, packfiles
and the smart-HTTP protocol are implemented here on `node:crypto` (SHA-1) and
`node:zlib`.

## Architecture: an actor per repository

Each repository is an **actor** with its own mailbox — a FIFO promise chain.
Every operation on a repository (a REST write, a contents commit, a squash
merge, a `git push`, an MCP tool call, a GraphQL mutation) is posted to that
repository's mailbox and runs only after the messages ahead of it finish, so
per-repo state is never interleaved and needs no locks.

A lightweight **supervisor** (the `Forge` class) owns the actor registry and
the repository lifecycle. The **git object pool is shared**: blobs, trees and
commits are content-addressed and immutable, so actors can read them freely;
only ref tips and the issue/pull records live inside the actors.

## Surfaces

- **REST v3** under `/api/v3` — repositories, contents, branches, commits,
  labels, issues, comments, pull requests and squash merges.
- **Git smart HTTP** at `/{owner}/{repo}.git` — `git-upload-pack` protocol v2
  (capability advertisement, `ls-refs`, `fetch` with shallow/deepen support)
  with a v0 side-band-64k fallback, and v0 `git-receive-pack` with
  `report-status`, `side-band-64k` and `delete-refs`. Non-fast-forward updates
  are refused per ref while the rest of the push still applies.
- **GraphQL** at `/api/graphql` — viewer/repository/issue/pull-request reads,
  the introspection probes `gh` performs, Relay-style global ids, cursor
  pagination, and the create/close/merge/comment mutations.
- **MCP** at `/mcp` — JSON-RPC 2.0 streamable HTTP: `server/discover`,
  the `initialize` handshake, and six tools (`create_repo`, `get_repo`,
  `create_issue`, `list_issues`, `create_pull_request`,
  `merge_pull_request`) acting on the same actors as REST.

Every surface requires `Authorization: Bearer <$MAKEFUN_SHOP_TOKEN>`.

## Run it

```sh
node main.ts
```

`main.ts` performs the trial lifecycle: it needs `MAKEFUN_ENV_URL` in the
environment, binds an ephemeral port, POSTs `{"port": N}` to
`$MAKEFUN_ENV_URL/register`, then polls `$MAKEFUN_ENV_URL/done` until the
environment answers `{"done": true}`, and exits 0.
