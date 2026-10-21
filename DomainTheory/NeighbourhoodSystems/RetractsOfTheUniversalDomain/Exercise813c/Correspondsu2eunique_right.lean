/-ai
If one set of natural numbers corresponds to two sets of points of Cantor space, those two sets are equal.

Each correspondence supplies a formula. The two formulas have the same evaluation on the natural numbers, so they are semantically equivalent, and semantic equivalence equates their evaluations on Cantor space.
ai-/
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


theorem Corresponds.unique_right {X : Set ℕ} {Y₁ Y₂ : Set (ℕ → Bool)}
    (h1 : Corresponds X Y₁) (h2 : Corresponds X Y₂) : Y₁ = Y₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  have hse : SemanticEquiv φ ψ := semanticEquiv_iff_evalSet_eq.mpr (hφX.trans hψX.symm)
  rw [← hφY, ← hψY, semanticEquiv_iff_evalSet'_eq.mp hse]

end DomainTheory.NeighbourhoodSystems
