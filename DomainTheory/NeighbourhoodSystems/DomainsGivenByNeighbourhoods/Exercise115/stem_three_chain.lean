/-ai
The stem domain contains a strict three-element chain: the principal filter of the whole set of natural numbers, then the principal filter of {0, 1}, then the principal filter of {0}.

The first step is the strict comparison of principal filters along the inclusion of {0, 1} in the whole set. Equality of those sets would put 2 in {0, 1}. The second step is the strict comparison along the inclusion of {0} in {0, 1}. Equality of those sets would put 1 in {0}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stem_mem_univ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stem_mem_pair
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stem_mem_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stem_principal_lt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Stem contains a strict 3-chain** `⊥ = ↑ℕ ⊏ ↑{0,1} ⊏ ↑{0}` — the structural feature that
distinguishes it from `flat`. -/
theorem stem_three_chain : ∃ a b c : stem.Element, a < b ∧ b < c := by
  refine ⟨stem.principal stem_mem_univ, stem.principal stem_mem_pair,
    stem.principal stem_mem_zero, ?_, ?_⟩
  · refine stem_principal_lt stem_mem_univ stem_mem_pair (Set.subset_univ _) ?_
    intro h
    have : (2 : ℕ) ∈ ({0, 1} : Set ℕ) := h ▸ Set.mem_univ 2
    simp at this
  · refine stem_principal_lt stem_mem_pair stem_mem_zero
      (Set.singleton_subset_iff.mpr (by simp)) ?_
    intro h
    have : (1 : ℕ) ∈ ({0} : Set ℕ) := h ▸ (by simp : (1 : ℕ) ∈ ({0, 1} : Set ℕ))
    simp at this

end DomainTheory.NeighbourhoodSystems.Exercise115
