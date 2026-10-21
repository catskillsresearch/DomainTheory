/-ai
The second child of a node code is strictly smaller than the node code.

The tag of a node code is positive, so its payload is strictly smaller than the code. The second child is at most that payload, and the two comparisons give the strict inequality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nodeCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.unpair_snd_lt_of_unpair_fst_pos

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TermAlgebra

theorem nodeCode_snd_lt (t1 t2 : ℕ) : t2 < nodeCode t1 t2 := by
  have hpos : 0 < (nodeCode t1 t2).unpair.1 := by
    unfold nodeCode; rw [unpair_pair_fst]; omega
  have hsnd : (nodeCode t1 t2).unpair.2 < nodeCode t1 t2 :=
    unpair_snd_lt_of_unpair_fst_pos hpos
  have ht2 : t2 ≤ (nodeCode t1 t2).unpair.2 := by
    unfold nodeCode; rw [unpair_pair_snd]; exact le_pair_right t1 t2
  omega

end TermAlgebra

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
