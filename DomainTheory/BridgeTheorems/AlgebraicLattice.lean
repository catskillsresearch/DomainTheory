module

public import DomainTheory.BridgeTheorems.IsCompactElement
import Mathlib.Tactic.Continuity.Init

@[expose] public section

namespace DomainTheory.BridgeTheorems

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

class AlgebraicLattice (D : Type*) [CompleteLattice D] : Prop where
  out : ∀ y : D,
    let S := {x : D | IsCompactElement x ∧ x ≤ y}
    S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧ sSup S = y

end IdealCompletionToContinuousLattice

end DomainTheory.BridgeTheorems
