module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smashRetraction_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smash_subsystem_prod
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.mem_toElementMap_retractionOfSubsystem_smash
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.exists_smash_witness

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






/-- **Scott's `smash` combinator equals Proposition 8.2's canonical subsystem retraction.** Both
sides agree with `smashRetraction_mem_iff`'s closed form: the `Z = master` branch matches (both
sides always admit the master witness `Y = (smash D E).master`), and the "genuine pair" branch
matches by `exists_smash_witness` (`←`) and a direct case split on `(smash D E).mem Y` (`→`, using
that `Y ⊆ (prod D E).master` sandwiches `Z = master` when `Y` is itself the master, and that
`z.fst.mem`/`z.snd.mem` of a proper `Y`'s factors forces both coordinates non-`⊥`, `mem_bot`). -/
theorem smashRetraction_eq_retractionOfSubsystem :
    smashRetraction (D := D) (E := E) = Subsystem.retractionOfSubsystem smash_subsystem_prod := by
  apply ext_of_toElementMap
  intro z
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff, mem_toElementMap_retractionOfSubsystem_smash]
  constructor
  · rintro ⟨hPZ, rfl | ⟨hx, hy, hzZ⟩⟩
    · exact ⟨hPZ, (prod D E).master, Exercise510.smash_mem_iff.mpr (Or.inl rfl), z.master_mem,
        subset_rfl⟩
    · exact ⟨hPZ, exists_smash_witness hx hy hzZ⟩
  · rintro ⟨hPZ, Y, hSY, hzY, hYZ⟩
    rcases Exercise510.smash_mem_iff.mp hSY with rfl | ⟨YA, YB, hYA, hYAne, hYB, hYBne, rfl⟩
    · exact ⟨hPZ, Or.inl (Set.Subset.antisymm ((prod D E).sub_master hPZ) hYZ)⟩
    · have hzfYA : z.fst.mem YA := mem_fst.mpr ⟨hYA, ((prod_mem_split hYA hYB).mp hzY).1⟩
      have hzsYB : z.snd.mem YB := mem_snd.mpr ⟨hYB, ((prod_mem_split hYA hYB).mp hzY).2⟩
      refine ⟨hPZ, Or.inr ⟨?_, ?_, z.up_mem hzY hPZ hYZ⟩⟩
      · intro hxbot; rw [hxbot, mem_bot] at hzfYA; exact hYAne hzfYA
      · intro hybot; rw [hybot, mem_bot] at hzsYB; exact hYBne hzsYB

end Smash
end DomainTheory.NeighbourhoodSystems
