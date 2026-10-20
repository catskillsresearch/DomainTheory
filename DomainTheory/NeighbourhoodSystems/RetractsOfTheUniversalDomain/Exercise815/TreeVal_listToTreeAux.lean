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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_leaf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_node
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.listToTreeAux
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

theorem TreeVal_listToTreeAux (acc : ℕ) (l : List ℕ) :
    TreeVal r (listToTreeAux acc l) = l.foldl (fun a j => Uinter a (r j)) (TreeVal r acc) := by
  induction l generalizing acc with
  | nil => simp [listToTreeAux]
  | cons j l ih =>
    simp only [listToTreeAux, List.foldl_cons]
    rw [ih, TreeVal_node, TreeVal_leaf]

end TreeVal2

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
