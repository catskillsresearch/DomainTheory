module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.ofSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystem_ofSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.ofSubsystem_toSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section OrderIso

variable (P : ComputablePresentation D)

/-- **Subgoal 3, capstone.** `SubD.Element ≃o {D' ∣ D' ◁ D}` — fully choice-free. Forward map
`toSubsystem`, inverse `ofSubsystem`; order preservation/reflection reduces via Scott's remark
(`Subsystem.subsystem_iff_subset_of_common`) to `mem_nbhdGen_iff` applied pointwise. -/
def subsystemIso : (SubD P).Element ≃o {D' : NeighborhoodSystem α // D' ◁ D} where
  toFun := toSubsystem P
  invFun x := ofSubsystem P x.1 x.2
  left_inv := ofSubsystem_toSubsystem P
  right_inv x := toSubsystem_ofSubsystem P x.1 x.2
  map_rel_iff' := by
    intro a b
    show toSubsystemSys P a ◁ toSubsystemSys P b ↔ (∀ N, a.mem N → b.mem N)
    rw [Subsystem.subsystem_iff_subset_of_common (toSubsystemSys_subsystem P a)
      (toSubsystemSys_subsystem P b)]
    constructor
    · intro hYsub N hN
      obtain ⟨js, rfl⟩ := a.sub hN
      exact (mem_nbhdGen_iff P b js).mpr
        (fun i hi => hYsub ((mem_nbhdGen_iff P a js).mp hN i hi))
    · rintro hab Y ⟨js, haj, hY⟩
      exact ⟨js, hab (nbhdGen P js) haj, hY⟩

end OrderIso

end DomainTheory.NeighbourhoodSystems
