module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smashRetraction_mem_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






theorem smashRetraction_le_idMap : smashRetraction (D := D) (E := E) ≤ idMap (prod D E) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [toElementMap_idMap]
  intro Z hZ
  rw [smashRetraction_mem_iff] at hZ
  rcases hZ with ⟨hPZ, rfl | ⟨-, -, hzZ⟩⟩
  · exact z.master_mem
  · exact hzZ

end Smash
end DomainTheory.NeighbourhoodSystems
