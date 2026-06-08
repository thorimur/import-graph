module

import all ImportGraph.Shake.Algebra

open Lean Lake Shake

def _root_.Lean.Environment.transitiveClosureOf (env : Environment)
    (imps : Array Import) (transDeps : Array Needs) : Needs :=
  imps.foldl (init := .empty) fun needs imp =>
    imp.addTransitiveClosure needs (env.getModuleIdx? imp.module |>.get!) transDeps

@[inline] def _root_.Lean.Environment.transNeeds (env : Environment) (transDeps : Array Needs) :
    Needs :=
  env.transitiveClosureOf env.header.imports transDeps
