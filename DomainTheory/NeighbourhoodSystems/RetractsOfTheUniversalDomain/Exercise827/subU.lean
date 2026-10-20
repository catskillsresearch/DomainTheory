/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **`sub`, regarded as a finitary projection of `𝒰` itself** (the exercise's opening sentence):
conjugate Theorem 8.6(b)'s `subApprox : (𝒰→𝒰)→(𝒰→𝒰)` through the fixed pair `i_→, j_→`
(Definition 8.9), exactly as `a→b` is built from `λf.b∘f∘a` in `Definition89.lean`. -/
noncomputable def subU : ApproximableMap U U :=
  iArrow.comp (Sub8_6.subApprox.comp jArrow)

end DomainTheory.NeighbourhoodSystems
