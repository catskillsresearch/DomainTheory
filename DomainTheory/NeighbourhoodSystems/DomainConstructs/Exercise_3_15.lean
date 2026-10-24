module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_14

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
/- concordance: source L1436 EXERCISE 3.15 product isomorphisms -/
/-- **Exercise 3.15 (empty product).** `𝟙` is a right unit: `𝒟 × 𝟙 ≅ 𝒟`. -/
def prodUnitD (V₀ : NeighborhoodSystem α) :
    (prod V₀ unitSys).Element ≃o V₀.Element :=
  (prodEquiv V₀ unitSys).trans (prodUniqueOrderIso _ _)

/-- **Exercise 3.15 (empty product).** `𝟙` is a left unit: `𝟙 × 𝒟 ≅ 𝒟`. -/
def unitProdD (V₀ : NeighborhoodSystem α) :
    (prod unitSys V₀).Element ≃o V₀.Element :=
  (prodEquiv unitSys V₀).trans (uniqueProdOrderIso _ _)

/-- **Exercise 3.15(iii).** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'`. -/
theorem Isomorphic.prod (h₀ : V₀ ≅ᴰ V₀') (h₁ : V₁ ≅ᴰ V₁') : prod V₀ V₁ ≅ᴰ prod V₀' V₁' :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨prodCongrD e₀ e₁⟩

/-- **Exercise 3.15(ii).** `𝒟₀ × (𝒟₁ × 𝒟₂) ≅ (𝒟₀ × 𝒟₁) × 𝒟₂`. -/
theorem prod_assoc_isomorphic : prod V₀ (prod V₁ V₂) ≅ᴰ prod (prod V₀ V₁) V₂ :=
  ⟨prodAssocD V₀ V₁ V₂⟩

/-- **Exercise 3.15(i).** `𝒟₀ × 𝒟₁ ≅ 𝒟₁ × 𝒟₀`. -/
theorem prod_comm_isomorphic : prod V₀ V₁ ≅ᴰ prod V₁ V₀ := ⟨prodCommD V₀ V₁⟩
end

section
set_option linter.unusedVariables false

theorem example_315.{u_1, u_2, u_4, u_5, u_3} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α (Sum β γ)) (Sum (Sum α β) γ)
      (@DomainTheory.NeighbourhoodSystems.prod α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
      (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α (Sum β γ)) (Sum (Sum α β) γ)
      (@DomainTheory.NeighbourhoodSystems.prod α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
      (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
    @DomainTheory.NeighbourhoodSystems.prod_comm_isomorphic @DomainTheory.NeighbourhoodSystems.Isomorphic.prod)
  @DomainTheory.NeighbourhoodSystems.prod_assoc_isomorphic
end

section
open NeighborhoodSystem
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

theorem prod_unit_isomorphic : prod V₀ unitSys ≅ᴰ V₀ := ⟨prodUnitD V₀⟩

theorem unit_prod_isomorphic : prod unitSys V₀ ≅ᴰ V₀ := ⟨unitProdD V₀⟩
end

section
open NeighborhoodSystem
variable {α : Type*}

/-- The `i`-th *fiber* of a set `W ⊆ ℕ × α`: the tokens appearing in copy `i`. -/
def fiber (W : Set (ℕ × α)) (i : ℕ) : Set α := {a | (i, a) ∈ W}

@[simp] theorem mem_fiber {W : Set (ℕ × α)} {i : ℕ} {a : α} : a ∈ fiber W i ↔ (i, a) ∈ W := Iff.rfl

theorem eq_of_fiber_eq {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i = fiber W' i) : W = W' := by
  ext ⟨i, a⟩
  exact Set.ext_iff.mp (h i) a

theorem fiber_inter (W W' : Set (ℕ × α)) (i : ℕ) :
    fiber (W ∩ W') i = fiber W i ∩ fiber W' i := rfl

theorem fiber_mono {W W' : Set (ℕ × α)} (h : W ⊆ W') (i : ℕ) : fiber W i ⊆ fiber W' i :=
  fun _ ha => h ha
end

section
open NeighborhoodSystem
variable {α : Type*}
variable (V : NeighborhoodSystem α)

/-- The `𝒟^∞`-neighbourhood pinning copy `n` to `X` and leaving all other copies at `Δ`: Scott's
`Δ^∞ ∩ (1ⁿ0X)`, i.e. the combination with `Xₙ = X` and `Xₘ = Δ` for `m ≠ n`. -/
def single (n : ℕ) (X : Set α) : Set (ℕ × α) :=
  {p | if p.1 = n then p.2 ∈ X else p.2 ∈ V.master}
end

section
open NeighborhoodSystem
variable {α : Type*}
variable (V : NeighborhoodSystem α)
variable {V}

@[simp] theorem fiber_single_self (n : ℕ) (X : Set α) : fiber (single V n X) n = X := by
  ext a; simp [fiber, single]

theorem fiber_single_ne {n i : ℕ} (h : i ≠ n) (X : Set α) : fiber (single V n X) i = V.master := by
  ext a; simp [fiber, single, h]

end
end DomainTheory.NeighbourhoodSystems
end
