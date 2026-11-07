module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.optimalFix

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

/-- Scott's Exercise 4.16: optimal fixed points of monotone maps on nonempty fixed sets. -/
theorem example_416 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element),
      Monotone f → ∀ (S : Set V.Element) (hS : S.Nonempty),
        (∀ s ∈ S, f s = s) → f (V.sInf S hS) ≤ V.sInf S hS) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element)
      (hf : Monotone f) (S : Set V.Element) (hS : S.Nonempty)
      (hfix : ∀ s ∈ S, f s = s) {s : V.Element},
      s ∈ S → ∃ ub, optimalFix f hf S hS hfix ≤ ub ∧ s ≤ ub) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (f : V.Element → V.Element)
      (hf : Monotone f) (S : Set V.Element) (hS : S.Nonempty)
      (hfix : ∀ s ∈ S, f s = s) {s : V.Element},
      s ∈ S → optimalFix f hf S hS hfix ≤ s) :=
  ⟨@f_sInf_le, @optimalFix_consistent, @optimalFix_le⟩
