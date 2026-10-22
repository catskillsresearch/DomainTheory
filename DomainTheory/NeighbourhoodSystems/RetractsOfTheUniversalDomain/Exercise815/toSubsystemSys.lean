module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.master_mem_finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_sub_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_sub_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.interFrom_append_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section OrderIso

variable (P : ComputablePresentation D)

/-- **Backward direction: a filter of `SubD` induces a subsystem.** The neighbourhoods are the
`Fin(js)`-members for lists `js` confirmed by the filter `x`. -/
def toSubsystemSys (x : (SubD P).Element) : NeighborhoodSystem α where
  mem Y := ∃ js, x.mem (nbhdGen P js) ∧ Y ∈ finGen P js
  master := D.master
  master_nonempty := D.master_nonempty
  master_mem := ⟨[], x.master_mem, master_mem_finGen P []⟩
  inter_mem := by
    rintro X Y Z ⟨js1, hx1, hX⟩ ⟨js2, hx2, hY⟩ ⟨js3, _, hZ⟩ hZsub
    have hDX := finGen_sub_mem P hX
    have hDY := finGen_sub_mem P hY
    have hDZ := finGen_sub_mem P hZ
    obtain ⟨sub1, hsub1, _, hXeq⟩ := hX
    obtain ⟨sub2, hsub2, _, hYeq⟩ := hY
    refine ⟨js1 ++ js2, nbhdGen_inter P js1 js2 ▸ x.inter_mem hx1 hx2,
      sub1 ++ sub2, hsub1.append hsub2, D.inter_mem hDX hDY hDZ hZsub, ?_⟩
    rw [interFrom_append_eq, hXeq, hYeq]
  sub_master := fun ⟨_, _, hY⟩ => finGen_sub_master P hY

end OrderIso

end DomainTheory.NeighbourhoodSystems
