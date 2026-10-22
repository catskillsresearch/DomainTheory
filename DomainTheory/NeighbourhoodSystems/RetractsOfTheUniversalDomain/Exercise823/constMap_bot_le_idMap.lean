module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}


theorem constMap_bot_le_idMap (E : NeighborhoodSystem α) :
    constMap E E.bot ≤ idMap E := by
  rintro X Z hr
  rw [constMap_rel, mem_bot] at hr
  obtain ⟨hX, rfl⟩ := hr
  exact ⟨hX, E.master_mem, E.sub_master hX⟩

end Exercise823
end DomainTheory.NeighbourhoodSystems
