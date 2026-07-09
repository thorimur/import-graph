/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import ImportGraphTest.FindHome.Harness

/-!
# Golden-file tests for `#find_home`

Each `#lake_serve` command below spawns `lake serve` in the fixture package
`ImportGraphTest/FindHome/findHomeB`, opens the given fixture file, waits for its diagnostics, and re-logs
them here. See `ImportGraphTest/FindHome/Harness.lean` for the harness and
`ImportGraphTest/FindHome/README.md` for the overall design.

TODO(#find_home WIP): the `#guard_msgs` golden expectations are commented out below,
since `#find_home` is still in progress. Each commented block records the *actual* output
captured on 2026-07-09 — which is not necessarily the *correct* output; the fixture files
document what to expect. Note in particular that every output currently begins with the
debug `logInfo` of `minimals` in the `#find_home` elab (`ImportGraph/Tools/FindHome.lean`,
"`logInfo m!"{minimals.toArray.map ...}"`"), which presumably goes away before these are
finalized. Once a scenario's output is verified, uncomment its golden block and delete
the bare `#lake_serve` that follows it.
-/

open ImportGraph.Test.Serve

-- Prepare the fixture packages (syncing their toolchains, regenerating their manifests,
-- and building — which also builds `importGraph` itself as a path dependency), so each
-- `#lake_serve` below only pays server startup.
#lake_setup "ImportGraphTest/FindHome/findHomeA"
#lake_setup "ImportGraphTest/FindHome/findHomeB"

/-! ## Core algorithm: cross-package meet

Expected: upstream suggestion pointing at `FindHomeA.Meet` in package
`findHomeA`. -/

/-
/--
info: @10:0-11:39:
[(FindHomeA, [FindHomeA.Meet]), ([anonymous], [FindHomeA.Meet])]
---
info: @10:0-11:39:
This command can be upstreamed to `FindHomeA` in `findHomeA`! Specifically:
  • FindHomeA.Meet

[copy] [copy source]

▼ More information
  ▼ Minimal imports
    import FindHomeA.ComponentA
    import FindHomeA.ComponentB
  New constants
    • crossPackage
-/
#guard_msgs in
#lake_serve "ImportGraphTest/FindHome/findHomeB" FindHomeB.CrossPackage
-/
#lake_serve "ImportGraphTest/FindHome/findHomeB" FindHomeB.CrossPackage

/-! ## In-current-library move

Expected: "In the current library, this command can be moved to: `FindHomeB.Local1`".

Observed instead: the *upstream* message ("can be upstreamed to `FindHomeB` in
`findHomeB`"), i.e. the `root == mainRoot` branch was not taken — the main module of the
served file does not seem to match `FindHomeB` here. Worth investigating in `#find_home`.
-/


/--
info: @10:0-11:42:
[(FindHomeB, [FindHomeB.Local1]), ([anonymous], [FindHomeB.Local1])]
---
info: @10:0-11:42:
This command can be upstreamed to `FindHomeB` in `findHomeB`! Specifically:
  • FindHomeB.Local1

[copy] [copy source]

▼ More information
  ▼ Minimal imports
    import FindHomeB.Local1
  New constants
    • inLibrary
-/
#guard_msgs in
#lake_serve "ImportGraphTest/FindHome/findHomeB" FindHomeB.InLibrary

/-! ## Edge case: (almost) no dependencies

Expected: suggestions as high as possible (core modules), and next to no needs.

Observed instead: a very large needs set — `Lake.CLI.Shake`, many `Std`/`Lean` internals,
`ImportGraph.Graph.TransitiveClosure`, and even `FindHomeA.ComponentA`/`ComponentB` are
all reported as places `noDeps : Nat := 1` could be upstreamed to (while "More
information" simultaneously says "No imports required."). This looks like the needs of
the `#find_home` machinery itself (or of the file's imports) leaking into the
declaration's needs. The output is large and clearly wrong, so no golden is recorded yet;
see this scenario's output via the bare `#lake_serve` below. -/

-- #guard_msgs in
#lake_serve "ImportGraphTest/FindHome/findHomeB" FindHomeB.NoDeps

/-! ## Edge case: auxiliary declarations from earlier in the file

Expected: the "depends on earlier declarations in this file" message
listing `auxHelper`, with homes accounting for both declarations' needs
(`FindHomeA.Meet`). -/

/-
/--
info: @13:0-14:38:
[(FindHomeA, [FindHomeA.Meet]), ([anonymous], [FindHomeA.Meet])]
---
info: @13:0-14:38:
This command depends on earlier declarations in this file:
  • auxHelper
Consider running `#find_home` on those first.

This command (and its dependencies from this file) can be upstreamed to `FindHomeA` in `findHomeA`! Specifically:
  • FindHomeA.Meet

[copy] [copy source - without dependencies]

▼ More information
  ▼ Minimal imports
    import FindHomeA.ComponentA
    import FindHomeA.ComponentB
  New constants
    • usesAux
  Auxiliary constants
    • auxHelper
-/
#guard_msgs in
#lake_serve "ImportGraphTest/FindHome/findHomeB" FindHomeB.AuxDecl
-/
#lake_serve "ImportGraphTest/FindHome/findHomeB" FindHomeB.AuxDecl

/-! ## Edge case: mutual blocks

Expected: home accounts for `compA` (used by `mutualOdd`), i.e.
`FindHomeA.ComponentA`. Note that the "New constants" list currently includes
implementation-detail constants (`._f`, `.match_1`, `._unsafe_rec`, `._sunfold`), which
may or may not be desirable in the display. -/

/--
info: @9:0-17:3:
[(FindHomeA, [FindHomeA.ComponentA]), ([anonymous], [FindHomeA.ComponentA])]
---
info: @9:0-17:3:
This command can be upstreamed to `FindHomeA` in `findHomeA`! Specifically:
  • FindHomeA.ComponentA

[copy] [copy source]

▼ More information
  ▼ Minimal imports
    import FindHomeA.ComponentA
  New constants
    • mutualEven._sunfold
    • mutualOdd._sunfold
    • mutualEven._unsafe_rec
    • mutualOdd._unsafe_rec
    • mutualEven
    • mutualOdd
    • mutualEven.match_1
    • mutualEven._f
    • mutualOdd._f
-/
#guard_msgs in
#lake_serve "ImportGraphTest/FindHome/findHomeB" FindHomeB.MutualBlock

/-! ## Edge case: command producing no declarations

Expected: warning that the command did not produce any declarations. (The
`info: 2` is the output of the `#eval` itself.) -/


/--
info: @8:0-8:5:
2
---
warning: @7:0-7:10:
This command did not produce any declarations.
-/
#guard_msgs in
#lake_serve "ImportGraphTest/FindHome/findHomeB" FindHomeB.NoDecls
