/-ai
For two correspondences, the set of natural numbers of the first is contained in the set of natural numbers of the second if and only if the same inclusion holds for the two sets of points of Cantor space.

Each correspondence is given by a formula, and substituting those evaluations reduces the claim to a comparison of evaluations. Inclusion of the evaluations on the natural numbers is entailment, which is inclusion of the Cantor-space evaluations, and the same chain runs from the Cantor-space inclusion back to the inclusion on the natural numbers.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.entails_iff_evalSet'_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Corresponds

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- `Corresponds` also matches `⊆` — i.e. it is an order-isomorphism between the two concrete
algebras, not just a bijection. -/
theorem Corresponds.subset_iff {X₁ X₂ : Set ℕ} {Y₁ Y₂ : Set (ℕ → Bool)}
    (h1 : Corresponds X₁ Y₁) (h2 : Corresponds X₂ Y₂) : X₁ ⊆ X₂ ↔ Y₁ ⊆ Y₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  subst hφX; subst hφY; subst hψX; subst hψY
  exact ⟨fun hsub => entails_iff_evalSet'_subset.mp (entails_iff_evalSet_subset.mpr hsub),
    fun hsub => entails_iff_evalSet_subset.mp (entails_iff_evalSet'_subset.mpr hsub)⟩

end DomainTheory.NeighbourhoodSystems
