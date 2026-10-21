/-ai
Evaluation of a node code is the universal intersection of the evaluations of its two children.

Each child is strictly smaller than the node code. The tag of a node is one, so the first selector equals zero and the second equals one, and the two payloads are the children. The fuel step therefore returns the universal intersection of the fuel values at the children, and those fuel values agree with the fuel-free evaluations because each child lies below the node.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nodeCode_fst_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nodeCode_snd_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_eq_QFuel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

/-- **Unfolding at a node.** -/
theorem TreeVal_node (t1 t2 : ℕ) :
    TreeVal r (nodeCode t1 t2) = Uinter (TreeVal r t1) (TreeVal r t2) := by
  have ht1 : t1 < nodeCode t1 t2 := nodeCode_fst_lt t1 t2
  have ht2 : t2 < nodeCode t1 t2 := nodeCode_snd_lt t1 t2
  have htag : (nodeCode t1 t2).unpair.1 = 1 := by unfold nodeCode; rw [unpair_pair_fst]
  have hc1 : (nodeCode t1 t2).unpair.2.unpair.1 = t1 := by
    unfold nodeCode; rw [unpair_pair_snd, unpair_pair_fst]
  have hc2 : (nodeCode t1 t2).unpair.2.unpair.2 = t2 := by
    unfold nodeCode; rw [unpair_pair_snd, unpair_pair_snd]
  have h1 : isOne (1 - (nodeCode t1 t2).unpair.1) = 0 := by rw [htag]; rfl
  have h2 : isOne (2 - (nodeCode t1 t2).unpair.1) = 1 := by rw [htag]; rfl
  show QBody r (QFuel r (nodeCode t1 t2)) (nodeCode t1 t2) = Uinter (TreeVal r t1) (TreeVal r t2)
  unfold QBody
  simp only [h1, h2, hc1, hc2, selectFn_zero, selectFn_one]
  rw [TreeVal_eq_QFuel r ht1, TreeVal_eq_QFuel r ht2]

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
