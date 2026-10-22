module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.evalSet'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Corresponds
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.idealOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.elementOfOpen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_genPoint_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_evalSet'_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_iff_exists_evalSet'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.semanticEquiv_iff_evalSet'_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.entails_iff_evalSet'_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.subset_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.nonempty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.dualFilter_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.univ_mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.not_empty_mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.inter_mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.up_mem_dualFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.empty_mem_idealOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.univ_not_mem_idealOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.union_mem_idealOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.down_mem_idealOf

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.generatedBy_iff_exists_evalSet
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems


theorem exists_corresponds_of_generatedBy_generator {X : Set ℕ} (hX : GeneratedBy generator X) :
    ∃ Y, Corresponds X Y := by
  obtain ⟨φ, hφ⟩ := generatedBy_iff_exists_evalSet.mp hX
  exact ⟨evalSet' φ, φ, hφ, rfl⟩

theorem Corresponds.unique_left {X₁ X₂ : Set ℕ} {Y : Set (ℕ → Bool)}
    (h1 : Corresponds X₁ Y) (h2 : Corresponds X₂ Y) : X₁ = X₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  have hse : SemanticEquiv φ ψ := semanticEquiv_iff_evalSet'_eq.mpr (hφY.trans hψY.symm)
  rw [← hφX, ← hψX, semanticEquiv_iff_evalSet_eq.mp hse]


end DomainTheory.NeighbourhoodSystems
