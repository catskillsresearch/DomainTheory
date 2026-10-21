/-ai
Z belongs to the subsystem retraction of the smash subsystem, applied to z, if and only if Z is a product neighbourhood and some smash neighbourhood Y of z is contained in Z.

A relational witness supplies a smash neighbourhood between a neighbourhood of z and Z, and upward closure of z moves membership onto that smash neighbourhood. Conversely, that smash neighbourhood is itself the relational witness, with the inclusion of it in itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smash_subsystem_prod

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






/-- The closed form of `Subsystem.retractionOfSubsystem`'s elementwise action, specialized to
`smash_subsystem_prod`, simplified using that `z` is already up-closed: the existential witness
`X ⊆ Y ⊆ Z` of Proposition 8.2's formula collapses to `z.mem Y` directly. -/
theorem mem_toElementMap_retractionOfSubsystem_smash {z : (prod D E).Element}
    {Z : Set (α ⊕ β)} :
    ((Subsystem.retractionOfSubsystem (smash_subsystem_prod (D := D) (E := E))).toElementMap z).mem
        Z ↔
      (prod D E).mem Z ∧ ∃ Y, (Exercise510.smash D E).mem Y ∧ z.mem Y ∧ Y ⊆ Z := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hzX, hrel⟩
    obtain ⟨hPX, hPZ, Y, hSY, hXY, hYZ⟩ := (Subsystem.retractionOfSubsystem_rel _).mp hrel
    exact ⟨hPZ, Y, hSY, z.up_mem hzX (smash_subsystem_prod.sub hSY) hXY, hYZ⟩
  · rintro ⟨hPZ, Y, hSY, hzY, hYZ⟩
    exact ⟨Y, hzY, (Subsystem.retractionOfSubsystem_rel _).mpr
      ⟨z.sub hzY, hPZ, Y, hSY, subset_rfl, hYZ⟩⟩

end Smash
end DomainTheory.NeighbourhoodSystems
