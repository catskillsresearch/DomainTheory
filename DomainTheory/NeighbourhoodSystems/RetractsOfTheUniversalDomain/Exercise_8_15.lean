module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SubsystemDomain

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem exercise_8_15 {α : Type*} {D : NeighborhoodSystem α} (hD : D.IsEffectivelyGiven) :
    ∃ V : NeighborhoodSystem (List ℕ), V.IsEffectivelyGiven ∧
      Nonempty (V.Element ≃o {D' : NeighborhoodSystem α // D' ◁ D}) :=
  subsystem_isEffectivelyGiven_of_isEffectivelyGiven hD

end
