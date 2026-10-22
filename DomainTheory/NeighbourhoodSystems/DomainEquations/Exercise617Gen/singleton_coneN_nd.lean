module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.singleton_subset_coneN

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

theorem singleton_coneN_nd (σ τ : Strn A) :
    ({τ} : Set (Strn A)) ⊆ coneN σ ∨ coneN σ ⊆ {τ} ∨ ({τ} : Set (Strn A)) ∩ coneN σ = ∅ := by
  by_cases h : σ <+: τ
  · exact Or.inl (singleton_subset_coneN.mpr h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_coneN, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hτ
    exact h hτ

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
