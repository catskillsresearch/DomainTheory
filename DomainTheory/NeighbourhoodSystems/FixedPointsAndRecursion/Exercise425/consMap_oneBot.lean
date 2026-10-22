module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- `1·(1ⁿ⊥) = 1ⁿ⁺¹⊥`. -/
theorem consMap_oneBot (n : ℕ) : consMap.toElementMap (oneBot n) = oneBot (n + 1) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : shift (tail n) ⊆ Y := (shift_mono hXX').trans hsub
    rwa [shift_tail] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨tail n, ⟨memC1_tail n, subset_rfl⟩, memC1_tail n, hY, ?_⟩
    rw [shift_tail]; exact hsub

end DomainTheory.NeighbourhoodSystems.Exercise425
