module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **Generic "swap-if" disjointness helper**: if `P` and `Q` are disjoint, then choosing `P` for
one Boolean and `Q` for a *different* Boolean always lands in disjoint sets, regardless of which
Boolean is `true`. -/
theorem if_swap_disjoint {γ : Type*} {P Q : Set γ} (hPQ : P ∩ Q = ∅) {b b' : Bool} (hbb' : b ≠ b') :
    (if b then P else Q) ∩ (if b' then P else Q) = ∅ := by
  rcases Bool.eq_false_or_eq_true b with hb | hb <;> rcases Bool.eq_false_or_eq_true b' with hb' | hb' <;>
    simp_all [Set.inter_comm]

end DomainTheory.NeighbourhoodSystems
