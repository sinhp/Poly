# checkdecls provenance and Lean migration

Vendored from https://github.com/PatrickMassot/checkdecls at commit
`3d425859e73fcfbef85b9638c2a91708ef4a22d4` (tag `lean4.18.0`, upstream
`master` as observed on 2026-10-10). Upstream had no Lean v4.34.1 release or
branch. The original Apache-2.0 license is retained in `LICENSE`.

Changes made for Poly's Lean v4.34.1 migration:

- Updated `lean-toolchain` from `leanprover/lean4:v4.18.0` to
  `leanprover/lean4:v4.34.1`.
- Ran `lake update`; Lake rewrote the empty manifest to schema 1.2.0 and
  added `fixedToolchain: false`. This package has no dependency repositories.
- No edits to `Main.lean` or `lakefile.lean` were required.

Verification on 2026-10-10 with Lean v4.34.1 on Linux:

- Standalone `lake update`: exit 0.
- Standalone `lake build`: exit 0, 4 jobs, no warnings.
- Executable smoke test in a separate tiny Lean package: an imported, existing
  declaration returned 0; an absent declaration returned 1 with its name;
  a nonexistent declaration-list file returned 1; no arguments returned 1.

The dependency is stored as ordinary source files, rather than an embedded Git
repository, so Poly's relative `vendor/checkdecls` path dependency is portable.
