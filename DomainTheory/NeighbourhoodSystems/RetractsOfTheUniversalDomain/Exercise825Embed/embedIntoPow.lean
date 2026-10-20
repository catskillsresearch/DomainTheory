/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The "singleton stack" embedding `D → D^∞`: `x ↦ ⟨x, ⊥, ⊥, …⟩`, i.e. `x` prepended to the all-`⊥`
stack. -/
def embedIntoPow : ApproximableMap V (iterSys V) :=
  (push V).comp (paired (idMap V) (constMap V (iterSys V).bot))

end DomainTheory.NeighbourhoodSystems
