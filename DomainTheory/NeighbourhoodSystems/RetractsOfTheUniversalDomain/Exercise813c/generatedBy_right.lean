module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_iff_exists_evalSet'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Corresponds

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.generatedBy_iff_exists_evalSet
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

theorem Corresponds.generatedBy_right {X : Set ℕ} {Y : Set (ℕ → Bool)} (h : Corresponds X Y) :
    GeneratedBy genPoint Y := by
  obtain ⟨φ, -, rfl⟩ := h; exact generatedBy_iff_exists_evalSet'.mpr ⟨φ, rfl⟩

end DomainTheory.NeighbourhoodSystems
