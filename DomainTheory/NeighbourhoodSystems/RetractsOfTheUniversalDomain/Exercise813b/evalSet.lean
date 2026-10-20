/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- The *same* recursion, but interpreted in `Set ℕ` via `generator` (`Exercise813a.lean`) instead
of an abstract Boolean — i.e. the specific homomorphism `var i ↦ generator i`. -/
def evalSet : Formula → Set ℕ
  | .var i => generator i
  | .bot => ∅
  | .top => Set.univ
  | .neg φ => (evalSet φ)ᶜ
  | .and φ ψ => evalSet φ ∩ evalSet ψ
  | .or φ ψ => evalSet φ ∪ evalSet ψ

end DomainTheory.NeighbourhoodSystems
