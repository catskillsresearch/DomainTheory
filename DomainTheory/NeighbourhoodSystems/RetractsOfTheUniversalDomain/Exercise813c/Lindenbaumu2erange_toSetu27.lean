module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic

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
