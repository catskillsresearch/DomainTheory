module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smash_subsystem_prod
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smashRetraction_eq_retractionOfSubsystem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






/-- **Example 8.4(b)(ii) (Scott 1981, PRG-19).** `smashRetraction` is a projection on `D × E`
whose fixed-point set is isomorphic to the smash product `Exercise510.smash D E`. -/
theorem example84b_smash :
    IsProjection (smashRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.smash D E).Element ≃o
        {z : (prod D E).Element // smashRetraction.toElementMap z = z}) := by
  rw [smashRetraction_eq_retractionOfSubsystem]
  exact ⟨Subsystem.isProjection_retractionOfSubsystem smash_subsystem_prod,
    ⟨Subsystem.elementIso smash_subsystem_prod⟩⟩

end Smash
end DomainTheory.NeighbourhoodSystems
