module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- **Exercise 4.13(3) (Scott 1981, PRG-19).** For any structured set `⟨Z, z, ·⟩` (`z : Z`,
`op : Z → Z`) there is a *unique* `s : ℕ → Z` with `s(0) = z` and `s(n⁺) = (s n)·`. This is the
choice-free recursion principle (`Nat.rec`); together with 4.13(1) it eliminates the circularity in
the proofs of 4.1 and 4.6. -/
theorem exists_unique_nat_rec {Z : Type*} (z : Z) (op : Z → Z) :
    ∃! s : ℕ → Z, s 0 = z ∧ ∀ n, s (n + 1) = op (s n) := by
  refine ⟨fun n => Nat.rec z (fun _ x => op x) n, ⟨rfl, fun _ => rfl⟩, ?_⟩
  rintro s ⟨h0, hsucc⟩
  funext n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hsucc k, ih]

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
