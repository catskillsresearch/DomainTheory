/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_beta


namespace DomainTheory.DataTypesAsLattices























































theorem primRecStep_graph_of (a f : Pomega) :
    graph (primRecStep a f) =
      funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f := by
  change graph (primRecStep a f) =
    funOf (funOf (interp (.lam 0 (.lam 1 (.lam 2 (.lam 3
      (.cond (.var 3) (.var 0)
        (.app (.app (.var 1) (.pred (.var 3)))
          (.app (.var 2) (.pred (.var 3))))))))) (fun _ => botElem)) a) f
  rw [theorem_2_2_beta, theorem_2_2_beta]
  apply congrArg graph
  funext u
  apply congrArg graph
  funext n
  simp [interp, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
