module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Lindenbaumu2erange_toSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Lindenbaumu2etoSet_injective
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.generatedBy_iff_exists_evalSet
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


theorem Lindenbaum.range_toSet' :
    Set.range Lindenbaum.toSet' = {Y | GeneratedBy genPoint Y} := by
  ext Y
  simp only [Set.mem_range, Set.mem_ofPred_eq, generatedBy_iff_exists_evalSet']
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.ind with
    | _ φ => exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨⟦φ⟧, rfl⟩

end DomainTheory.NeighbourhoodSystems
