module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.oneBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.oneElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.consMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.infElt
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.relateNToC1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.tail_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1_shift
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.singleton_tail_nd
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1_master

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- `1·(1ⁿ) = 1ⁿ⁺¹`. -/
theorem consMap_oneElem (n : ℕ) : consMap.toElementMap (oneElem n) = oneElem (n + 1) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : shift {n} ⊆ Y := (shift_mono hXX').trans hsub
    rwa [shift_singleton] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨{n}, ⟨memC1_singleton n, subset_rfl⟩, memC1_singleton n, hY, ?_⟩
    rw [shift_singleton]; exact hsub

end DomainTheory.NeighbourhoodSystems.Exercise425
