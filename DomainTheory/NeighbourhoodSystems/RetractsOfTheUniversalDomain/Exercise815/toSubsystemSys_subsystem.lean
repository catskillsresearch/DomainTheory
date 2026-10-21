/-ai
The neighbourhood system reconstructed from a filter of the system of finitely generated subsystems is a subsystem of the original system.

The masters agree. A reconstructed neighbourhood is a neighbourhood of the original system because it belongs to a finitely generated family. The intersection of two reconstructed neighbourhoods is again one: concatenate the generating lists, use closure of the filter under intersection, concatenate the selected sublists, and identify the combined intersection with the intersection of the two selected intersections.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_sub_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.interFrom_append_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section OrderIso

variable (P : ComputablePresentation D)

/-- **`toSubsystemSys x` is a genuine subsystem of `D`.** Uses the same `interFrom_append_eq`
witness-combination argument as `inter_mem`, without needing the extra `Z`-witness. -/
theorem toSubsystemSys_subsystem (x : (SubD P).Element) : toSubsystemSys P x ◁ D where
  master_eq := rfl
  sub := fun ⟨_, _, hY⟩ => finGen_sub_mem P hY
  inter_closed := by
    rintro X Y ⟨js1, hx1, hX⟩ ⟨js2, hx2, hY⟩ hXY
    obtain ⟨sub1, hsub1, _, hXeq⟩ := hX
    obtain ⟨sub2, hsub2, _, hYeq⟩ := hY
    refine ⟨js1 ++ js2, nbhdGen_inter P js1 js2 ▸ x.inter_mem hx1 hx2,
      sub1 ++ sub2, hsub1.append hsub2, hXY, ?_⟩
    rw [interFrom_append_eq, hXeq, hYeq]

end OrderIso

end DomainTheory.NeighbourhoodSystems
