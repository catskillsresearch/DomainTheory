/-ai
Whenever zero is never a successor and successor is injective, the carved-out subtype with the inherited zero and successor is a Peano model. The two ambient laws pass to the subtype along the underlying element. For induction, the pullback of the subset contains zero, because zero lies in the carved-out set and the zero of the subtype lies in the subset, and it is closed under successor, because a member's successor stays in the carved-out set and the successor step applies; induction for the carved-out set puts every carved-out element in the pullback, so the given element lies in the subset.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.zero_mem_nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.succ_mem_nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats_induction
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.Nat'
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.subZero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.subSucc

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- **Exercise 4.22 (Scott 1981, PRG-19).** The carved-out subset `N ⊆ N*`, with the inherited
`0` and `⁺`, is a model of **all three** Peano axioms — even though `N*` was only assumed to satisfy
(i) and (ii). Axioms (i)/(ii) are inherited; (iii) holds by minimality of the least fixed point. -/
def peanoSub (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    PeanoModel (Nat' zero succ) where
  zero := subZero zero succ
  succ := subSucc zero succ
  zero_ne_succ n h := hzero n.1 (Subtype.ext_iff.mp h)
  succ_injective a b h := Subtype.ext (hinj (Subtype.ext_iff.mp h))
  induction s h0 hstep := by
    -- pull `s` back to a subset of `N*`, show it is closed under `0`/`⁺`, apply `nats_induction`
    intro n
    have hsub : nats zero succ ⊆
        {m | ∃ h : m ∈ nats zero succ, (⟨m, h⟩ : Nat' zero succ) ∈ s} := by
      apply nats_induction zero succ
      · exact ⟨zero_mem_nats zero succ, h0⟩
      · rintro m ⟨hmnat, hms⟩
        exact ⟨succ_mem_nats zero succ hmnat, hstep ⟨m, hmnat⟩ hms⟩
    obtain ⟨_, hns⟩ := hsub n.2
    exact hns

end DomainTheory.NeighbourhoodSystems.Exercise422
