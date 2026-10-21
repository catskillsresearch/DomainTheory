/-ai
The first component of the left fold of the pure step along a list is the last index reached from the starting index.

Induct on the list. On the empty list the first component of the paired start is the starting index. On a cons the step advances the index to the head, and the inductive hypothesis says the remaining fold ends at the last index of the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


variable (P : ComputablePresentation V)


/-- The `foldCode` tracks the last index reached. -/
theorem fixPStep_foldl_fst (fincl : ℕ → ℕ) (c : ℕ) :
    ∀ (full : List ℕ) (prev fl : ℕ),
      (List.foldl (fixPStep fincl c) (Nat.pair prev fl) full).unpair.1 = gLastOf prev full := by
  intro full
  induction full with
  | nil =>
    intro prev fl
    show (Nat.pair prev fl).unpair.1 = prev
    exact unpair_pair_fst prev fl
  | cons b rest ih =>
    intro prev fl
    rw [List.foldl_cons]
    have hstep : fixPStep fincl c (Nat.pair prev fl) b
        = Nat.pair b (selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0) := by
      unfold fixPStep; simp only [unpair_pair_fst, unpair_pair_snd]
    rw [hstep, ih b (selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0)]
    rfl

end DomainTheory.NeighbourhoodSystems
