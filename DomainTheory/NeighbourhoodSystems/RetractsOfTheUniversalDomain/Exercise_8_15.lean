module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SubsystemDomain

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 8.15 (Scott 1981, PRG-19).** If `D` is effectively given, the domain of subsystems
`{D' ∣ D' ◁ D}` is (order-isomorphic to the elements of) an effectively given neighbourhood system. -/
theorem exercise_8_15 {α : Type*} {D : NeighborhoodSystem α} (hD : D.IsEffectivelyGiven) :
    ∃ V : NeighborhoodSystem (List ℕ), V.IsEffectivelyGiven ∧
      Nonempty (V.Element ≃o {D' : NeighborhoodSystem α // D' ◁ D}) :=
  subsystem_isEffectivelyGiven_of_isEffectivelyGiven hD

end
