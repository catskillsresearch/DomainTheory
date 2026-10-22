/-ai
Correspondence is preserved by intersection.

Each correspondence supplies a formula, and the conjunction of those formulas evaluates to the intersection on the natural numbers and to the intersection on Cantor space.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.evalSet'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Corresponds

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

theorem Corresponds.inter {X₁ X₂ : Set ℕ} {Y₁ Y₂ : Set (ℕ → Bool)}
    (h1 : Corresponds X₁ Y₁) (h2 : Corresponds X₂ Y₂) :
    Corresponds (X₁ ∩ X₂) (Y₁ ∩ Y₂) := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  refine ⟨.and φ ψ, ?_, ?_⟩
  · show evalSet φ ∩ evalSet ψ = X₁ ∩ X₂; rw [hφX, hψX]
  · show evalSet' φ ∩ evalSet' ψ = Y₁ ∩ Y₂; rw [hφY, hψY]

end DomainTheory.NeighbourhoodSystems
