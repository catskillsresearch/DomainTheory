module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_17
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_11
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
/- concordance: source L1543 EXERCISE 3.21 identity of step neighbourhoods -/
/-- **Exercise 3.21.** If the output is the master, `[Y, Δ₂]` is the whole function space. -/
theorem step_master_right (Y : Set α) (hY : V₀.mem Y) :
    (step Y V₁.master : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f
  simp only [mem_step, Set.mem_univ, iff_true]
  exact f.mono f.master_rel (V₀.sub_master hY) subset_rfl hY V₁.master_mem

theorem step_eq_univ_iff {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    (step Y Z : Set (ApproximableMap V₀ V₁)) = Set.univ ↔ Z = V₁.master := by
  constructor
  · intro h
    -- the empty-list least map relates `Y` only to `Δ₂`; it lies in `[Y, Z] = univ`
    have hmem : leastMap (V₀ := V₀) (V₁ := V₁) ([] : List (Set α × Set β))
        (by simp) (fun {X} _ => by rw [interYs_nil]; exact V₁.master_mem) ∈ step Y Z := by
      rw [h]; exact Set.mem_univ _
    rw [mem_step, leastMap_rel] at hmem
    have : V₁.master ⊆ Z := by rw [← interYs_nil V₁.master Y]; exact hmem.2.2
    exact Set.Subset.antisymm (V₁.sub_master hZ) this
  · rintro rfl; exact step_master_right Y hY

/-- **Exercise 3.21 (Scott 1981, PRG-19).** If `Z ≠ Δ₂`, the neighbourhood `[Y, Z]` determines both
endpoints: `[Y, Z] = [Y', Z']` implies `Y = Y'` and `Z = Z'`. -/
theorem step_eq_of_ne_master {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') (hZne : Z ≠ V₁.master)
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') : Y = Y' ∧ Z = Z' := by
  -- `Z' ≠ Δ₂` too, else `[Y', Z']` is the whole space and so is `[Y, Z]`, forcing `Z = Δ₂`
  have hZ'ne : Z' ≠ V₁.master := by
    intro hZ'eq
    rw [hZ'eq, step_master_right Y' hY'] at h
    exact hZne ((step_eq_univ_iff hY hZ).mp h)
  have hfeq := leastStep_eq_of_step_eq hY hZ hY' hZ' h
  -- `f₀.rel Y' Z'` and `f₀'.rel Y Z`, both with non-master outputs
  have h1 : (leastStep Y Z hY hZ).rel Y' Z' := by
    rw [hfeq]; exact (leastStep_mem hY' hZ')
  have h2 : (leastStep Y' Z' hY' hZ').rel Y Z := by
    rw [← hfeq]; exact (leastStep_mem hY hZ)
  rw [leastStep_rel hY hZ hY' hZ'] at h1
  rw [leastStep_rel hY' hZ' hY hZ] at h2
  -- from `h1`: `Y' ⊆ Y` and `Z ⊆ Z'`
  have hY'Y : Y' ⊆ Y := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h1
    exact hZ'ne (Set.Subset.antisymm (V₁.sub_master hZ') h1)
  have hZZ' : Z ⊆ Z' := by
    rw [interYs_single_subset_eq hZ hY'Y] at h1; exact h1
  -- from `h2`: `Y ⊆ Y'` and `Z' ⊆ Z`
  have hYY' : Y ⊆ Y' := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h2
    exact hZne (Set.Subset.antisymm (V₁.sub_master hZ) h2)
  have hZ'Z : Z' ⊆ Z := by
    rw [interYs_single_subset_eq hZ' hYY'] at h2; exact h2
  exact ⟨Set.Subset.antisymm hYY' hY'Y, Set.Subset.antisymm hZZ' hZ'Z⟩

/-- **Exercise 3.21 (Scott 1981, PRG-19).** The simple criterion for identity of function-space
neighbourhoods: `[Y, Z] = [Y', Z']` iff both outputs are the master `Δ₂`, or the pairs coincide. -/
theorem step_eq_iff {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') :
    (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z' ↔
      (Z = V₁.master ∧ Z' = V₁.master) ∨ (Y = Y' ∧ Z = Z') := by
  constructor
  · intro h
    by_cases hZeq : Z = V₁.master
    · refine Or.inl ⟨hZeq, ?_⟩
      rw [hZeq, step_master_right Y hY] at h
      exact (step_eq_univ_iff hY' hZ').mp h.symm
    · exact Or.inr (step_eq_of_ne_master hY hZ hY' hZ' hZeq h)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [step_master_right Y hY, step_master_right Y' hY']
    · rfl
end

section
set_option linter.unusedVariables false

theorem example_321.{u_1, u_2} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                Iff
                  (@Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z'))
                  (Or
                    (And (@Eq (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
                      (@Eq (Set β) Z' (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁)))
                    (And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                @Ne (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) →
                  @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z') →
                    And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (Y : Set α),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
      @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
        (@Set.univ (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                Iff
                  (@Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z'))
                  (Or
                    (And (@Eq (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
                      (@Eq (Set β) Z' (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁)))
                    (And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                @Ne (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) →
                  @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z') →
                    And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (Y : Set α),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
      @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
        (@Set.univ (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                Iff
                  (@Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z'))
                  (Or
                    (And (@Eq (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
                      (@Eq (Set β) Z' (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁)))
                    (And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                @Ne (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) →
                  @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z') →
                    And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))
    @DomainTheory.NeighbourhoodSystems.step_eq_iff @DomainTheory.NeighbourhoodSystems.step_eq_of_ne_master)
  @DomainTheory.NeighbourhoodSystems.step_master_right
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- The uncurried composition map `((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) × 𝒟₀ → 𝒟₂`, `⟨⟨g, f⟩, x⟩ ↦ g(f(x))`,
built from the inner evaluation `(𝒟₀→𝒟₁) × 𝒟₀ → 𝒟₁`, the outer evaluation `(𝒟₁→𝒟₂) × 𝒟₁ → 𝒟₂`,
and the product projections/pairing (Definition 3.3). -/
def compApp (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀) V₂ :=
  (evalMap V₁ V₂).comp
    (paired
      ((proj₀ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
        (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
      ((evalMap V₀ V₁).comp
        (paired
          ((proj₁ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
            (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
          (proj₁ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))))

end
end
end DomainTheory.NeighbourhoodSystems
end
