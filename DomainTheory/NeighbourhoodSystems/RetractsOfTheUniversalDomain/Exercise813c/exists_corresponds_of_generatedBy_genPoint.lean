module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.generatedBy_iff_exists_evalSet
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


theorem exists_corresponds_of_generatedBy_genPoint {Y : Set (ℕ → Bool)}
    (hY : GeneratedBy genPoint Y) : ∃ X, Corresponds X Y := by
  obtain ⟨φ, hφ⟩ := generatedBy_iff_exists_evalSet'.mp hY
  exact ⟨evalSet φ, φ, rfl, hφ⟩

end DomainTheory.NeighbourhoodSystems
