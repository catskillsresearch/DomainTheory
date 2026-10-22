module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_succ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- Thue–Morse prefixes are nested in the prefix order. -/
theorem tmList_prefix {n m : ℕ} (h : n ≤ m) : tmList n <+: tmList m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hlt | rfl
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (by rw [tmList_succ]; exact List.prefix_append _ _)
    · exact List.prefix_rfl

end DomainTheory.NeighbourhoodSystems.Exercise516
