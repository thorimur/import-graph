# `#find_home` test suites

`#find_home` only produces useful output when run in the language server, so these tests
take a golden-file approach built around a minimal Lean-side LSP client
([`Harness.lean`](Harness.lean)): an orchestrating Lean file spawns `lake serve` in a
fixture package, opens a fixture file over LSP, waits for its diagnostics via the
Lean-specific `textDocument/waitForDiagnostics` request, and re-logs them in the
orchestrating file — where `#guard_msgs` provides the golden-file comparison.

## Layout

```
ImportGraphTest/FindHome/
  Harness.lean          # the LSP client + the #lake_build / #lake_serve commands
  Serve.lean            # the CI orchestrator (imported by the ImportGraphTest runner)
  findHomeA/            # fixture package: ComponentA/ComponentB with meet FindHomeA.Meet
  findHomeB/            # fixture package: depends on findHomeA; contains the served files
test/personal/
  FindHomePersonal/     # interactive-only package; depends on batteries (git dependency)
```

Both CI fixture packages depend on `importGraph` via the relative path `../../..`, and
`findHomeB` depends on `findHomeA` via `../findHomeA` — so the suite covers homes in the
current library, in another local package, and in core, with no external git dependencies
beyond what `importGraph` itself already requires. (They also set
`packagesDir = "../../../.lake/packages"` so the `Cli` checkout is shared with the outer
workspace instead of re-cloned.)

The fixture packages' `lean-toolchain` and `lake-manifest.json` files are **gitignored
and regenerated**: `#lake_build` copies in the workspace root's `lean-toolchain` and runs
`lake update` before building, so they cannot go stale.

## CI suite

The orchestrator is [`Serve.lean`](Serve.lean); it runs as part of `lake test` (via the
`ImportGraphTest` library). It first issues `#lake_build` for the fixture packages
(toolchain sync + `lake update` + `lake build`), then one `#lake_serve` per scenario:

| Fixture module | Scenario |
| --- | --- |
| `FindHomeB.CrossPackage` | core algorithm: meet of two components lives in the *other* package (`FindHomeA.Meet`) |
| `FindHomeB.InLibrary` | in-current-library move (`FindHomeB.Local1`) |
| `FindHomeB.NoDeps` | edge case: no dependencies beyond the prelude |
| `FindHomeB.AuxDecl` | edge case: depends on an earlier declaration in the same file |
| `FindHomeB.MutualBlock` | edge case: mutual block |
| `FindHomeB.NoDecls` | edge case: command produces no declarations |

Some `#guard_msgs` golden expectations are still commented out (marked
`TODO(#find_home WIP)`) because `#find_home` is in progress. Until they are activated,
those scenarios still exercise the whole pipeline (fixture build, server startup, file
elaboration) and fail on harness/server errors, but do not pin down `#find_home`'s
output. Commented-out blocks record the output *actually observed* on 2026-07-09,
together with notes on whether it matches the expectation documented in the fixture
file. Once a scenario's output is verified correct, uncomment its block and delete the
bare `#lake_serve` that follows it.

Notes:

* Paths passed to `#lake_build`/`#lake_serve` are relative to the workspace root (the
  cwd both under `lake build` and in the language server); `#lake_serve` takes the module
  to serve as an identifier, resolved to a source file relative to the package directory.
* Each logged message carries the fixture diagnostic's range in its text, so golden files
  also record positions.
* Each `#lake_serve` has a 5-minute internal timeout, after which the server is killed
  and the command fails. (`#lake_build` currently has no timeout.)

## Personal (interactive) suite

`test/personal/FindHomePersonal` is *not* part of CI: it depends on `batteries` as a git
dependency and is meant to be used by opening files in the editor. Setup:

```
cd test/personal/FindHomePersonal
cp ../../../lean-toolchain .   # sync with the workspace toolchain
lake update                    # fetches batteries; adjust its rev in lakefile.toml if needed
lake build
```

Then open each file under `FindHomePersonal/` and follow the checklist in its module
docstring. Together they cover go-to-def on suggested module links for:

* **core** modules (toolchain source) — `CoreHome.lean`;
* modules in a **git**-path dependency (`.lake/packages/batteries/`) —
  `BatteriesHome.lean`;
* modules in a **relative**-path dependency (the `importGraph` working copy itself) —
  `RelativePathHome.lean`.

The CI fixture files under `findHomeB/FindHomeB/` are also useful interactively: opening
the `findHomeB` folder in the editor and visiting them shows the same output the harness
collects.
