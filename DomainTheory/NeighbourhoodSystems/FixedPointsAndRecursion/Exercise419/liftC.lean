/-ai
An approximable map from the sequence domain into a neighbourhood system is determined by a value on each partial element and a value on each total element, with partial values increasing along prefixes and each partial value below the total value of every extension. The relation holds when the domain neighbourhood is the cone of a string and the codomain neighbourhood belongs to the partial value, or the domain neighbourhood is a singleton and the codomain neighbourhood belongs to the total value. Cones and singletons are neighbourhoods, and a related codomain neighbourhood belongs to an element. The master neighbourhood is the cone of the empty string, which is the whole token set, and it is related through the master membership of the partial value on the empty string. For intersections, two cone witnesses name the same string, and the partial value is closed under intersection; a cone witness cannot equal a singleton witness; two singleton witnesses name the same string, and the total value is closed under intersection. For monotonicity, a smaller cone is the cone or the singleton of an extension, and the corresponding prefix hypothesis enlarges the codomain membership. A smaller singleton cannot be a cone. If it is a singleton, the inclusion forces the two strings to agree, and upward closure of the total value enlarges the codomain membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.not_cone_subset_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_nil
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_false
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_true

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

variable {β : Type*}

/-- A map `C → V` determined by its value `coneVal σ` on each partial element `σ⊥` and `singVal σ`
on each total element `σ`, provided (a) the partial values are monotone along prefixes and (b) a
partial value sits below the total value of any extending prefix. The relation says: a cone `σΣ*`
relates to the neighbourhoods of `coneVal σ`, and a singleton `{σ}` to those of `singVal σ`. -/
def liftC (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) :
    ApproximableMap C V where
  rel X Y := (∃ σ, X = cone σ ∧ (coneVal σ).mem Y) ∨ (∃ σ, X = {σ} ∧ (singVal σ).mem Y)
  rel_dom := by
    rintro X Y (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)
    · exact memC_cone σ
    · exact memC_singleton σ
  rel_cod := by
    rintro X Y (⟨σ, _, hY⟩ | ⟨σ, _, hY⟩)
    · exact (coneVal σ).sub hY
    · exact (singVal σ).sub hY
  master_rel := by
    refine Or.inl ⟨[], ?_, (coneVal []).master_mem⟩
    rw [C_master]; exact cone_nil.symm
  inter_right := by
    rintro X Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) (⟨σ', hX', hY'⟩ | ⟨σ', hX', hY'⟩)
    · have : σ = σ' := cone_injective hX'
      subst this
      exact Or.inl ⟨σ, rfl, (coneVal σ).inter_mem hY hY'⟩
    · exact absurd hX' (cone_ne_singleton σ σ')
    · exact absurd hX'.symm (cone_ne_singleton σ' σ)
    · have : σ = σ' := by rw [Set.singleton_eq_singleton_iff] at hX'; exact hX'
      subst this
      exact Or.inr ⟨σ, rfl, (singVal σ).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) hX'X hYY' hX' hY'
    · -- input is the cone `σΣ*`
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · -- `X' = cone τ ⊆ cone σ`, so `σ <+: τ`
        have hpre : σ <+: τ := cone_subset_cone.mp hX'X
        exact Or.inl ⟨τ, rfl, (coneVal τ).up_mem (hcone hpre Y hY) hY' hYY'⟩
      · -- `X' = {τ} ⊆ cone σ`, so `σ <+: τ`
        have hpre : σ <+: τ := singleton_subset_cone.mp hX'X
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem (hsing hpre Y hY) hY' hYY'⟩
    · -- input is the singleton `{σ}`
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · exact absurd hX'X (not_cone_subset_singleton τ σ)
      · have hτσ : τ = σ := by
          have := Set.singleton_subset_iff.mp hX'X
          rwa [Set.mem_singleton_iff] at this
        subst hτσ
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem hY hY' hYY'⟩

end DomainTheory.NeighbourhoodSystems.Exercise419
