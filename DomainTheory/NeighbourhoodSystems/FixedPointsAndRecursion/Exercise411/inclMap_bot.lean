module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.inclMap_toElementMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The inclusion is strict: `ι(⊥) = ⊥`. -/
theorem inclMap_bot (a : V.Element) : (inclMap a).toElementMap (relSystem a).bot = V.bot := by
  rw [inclMap_toElementMap]
  apply Element.ext
  intro Y
  rw [mem_bot]
  constructor
  · rintro ⟨hVY, W, _, hbW, hWY⟩
    rw [mem_bot] at hbW
    rw [hbW] at hWY
    exact Set.Subset.antisymm (V.sub_master hVY) hWY
  · rintro rfl
    exact ⟨V.master_mem, V.master, a.master_mem, (relSystem a).bot.master_mem, subset_rfl⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
