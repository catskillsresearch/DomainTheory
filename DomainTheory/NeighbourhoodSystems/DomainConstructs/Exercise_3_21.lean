module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem interYs_single_not_subset_eq {YX : Set α} {Z : Set β} {X : Set α}
    (hXY : ¬ X ⊆ YX) : interYs V₁.master [(YX, Z)] X = V₁.master := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨hm, _⟩; exact hm
  · intro hz
    exact ⟨hz, fun p hp hXp => by rw [List.mem_singleton] at hp; subst hp; exact absurd hXp hXY⟩

theorem interYs_single_subset_eq {YX : Set α} {Z : Set β} {X : Set α} (hZ : V₁.mem Z)
    (hXY : X ⊆ YX) : interYs V₁.master [(YX, Z)] X = Z := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨_, hall⟩; exact hall (YX, Z) (List.mem_singleton.mpr rfl) hXY
  · intro hz
    exact ⟨V₁.sub_master hZ hz, fun p hp _ => by rw [List.mem_singleton] at hp; subst hp; exact hz⟩

theorem stepCons {Y : Set α} {Z : Set β} (hZ : V₁.mem Z) :
    ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master [(Y, Z)] X) := by
  intro X _
  by_cases hXY : X ⊆ Y
  · rw [interYs_single_subset_eq hZ hXY]; exact hZ
  · rw [interYs_single_not_subset_eq hXY]; exact V₁.master_mem

def leastStep (Y : Set α) (Z : Set β) (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    ApproximableMap V₀ V₁ :=
  leastMap [(Y, Z)] (by rintro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hY, hZ⟩)
    (stepCons hZ)

theorem leastStep_le {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {f : ApproximableMap V₀ V₁} (hf : f ∈ step Y Z) : leastStep Y Z hY hZ ≤ f := by
  apply leastMap_le
  rw [stepFun_singleton]; exact hf

theorem leastStep_mem {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    leastStep Y Z hY hZ ∈ step Y Z := by
  have := leastMap_mem_stepFun (V₀ := V₀) (V₁ := V₁)
    (L := [(Y, Z)]) (by rintro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hY, hZ⟩)
    (stepCons hZ)
  rw [stepFun_singleton] at this
  exact this

theorem leastStep_eq_of_step_eq {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z')
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') :
    leastStep Y Z hY hZ = leastStep Y' Z' hY' hZ' := by
  apply le_antisymm
  · exact leastStep_le hY hZ (h ▸ leastStep_mem hY' hZ')
  · exact leastStep_le hY' hZ' (h.symm ▸ leastStep_mem hY hZ)

theorem leastStep_rel {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') :
    (leastStep Y Z hY hZ).rel Y' Z' ↔ interYs V₁.master [(Y, Z)] Y' ⊆ Z' := by
  rw [leastStep, leastMap_rel]
  exact ⟨fun h => h.2.2, fun h => ⟨hY', hZ', h⟩⟩

theorem step_master_right (Y : Set α) (hY : V₀.mem Y) :
    (step Y V₁.master : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f
  simp only [mem_step, Set.mem_univ, iff_true]
  exact f.mono f.master_rel (V₀.sub_master hY) subset_rfl hY V₁.master_mem

theorem step_eq_univ_iff {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    (step Y Z : Set (ApproximableMap V₀ V₁)) = Set.univ ↔ Z = V₁.master := by
  constructor
  · intro h

    have hmem : leastMap (V₀ := V₀) (V₁ := V₁) ([] : List (Set α × Set β))
        (by simp) (fun {X} _ => by rw [interYs_nil]; exact V₁.master_mem) ∈ step Y Z := by
      rw [h]; exact Set.mem_univ _
    rw [mem_step, leastMap_rel] at hmem
    have : V₁.master ⊆ Z := by rw [← interYs_nil V₁.master Y]; exact hmem.2.2
    exact Set.Subset.antisymm (V₁.sub_master hZ) this
  · rintro rfl; exact step_master_right Y hY

theorem step_eq_of_ne_master {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') (hZne : Z ≠ V₁.master)
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') : Y = Y' ∧ Z = Z' := by

  have hZ'ne : Z' ≠ V₁.master := by
    intro hZ'eq
    rw [hZ'eq, step_master_right Y' hY'] at h
    exact hZne ((step_eq_univ_iff hY hZ).mp h)
  have hfeq := leastStep_eq_of_step_eq hY hZ hY' hZ' h

  have h1 : (leastStep Y Z hY hZ).rel Y' Z' := by
    rw [hfeq]; exact (leastStep_mem hY' hZ')
  have h2 : (leastStep Y' Z' hY' hZ').rel Y Z := by
    rw [← hfeq]; exact (leastStep_mem hY hZ)
  rw [leastStep_rel hY hZ hY' hZ'] at h1
  rw [leastStep_rel hY' hZ' hY hZ] at h2

  have hY'Y : Y' ⊆ Y := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h1
    exact hZ'ne (Set.Subset.antisymm (V₁.sub_master hZ') h1)
  have hZZ' : Z ⊆ Z' := by
    rw [interYs_single_subset_eq hZ hY'Y] at h1; exact h1

  have hYY' : Y ⊆ Y' := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h2
    exact hZne (Set.Subset.antisymm (V₁.sub_master hZ) h2)
  have hZ'Z : Z' ⊆ Z := by
    rw [interYs_single_subset_eq hZ' hYY'] at h2; exact h2
  exact ⟨Set.Subset.antisymm hYY' hY'Y, Set.Subset.antisymm hZZ' hZ'Z⟩

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
end
end DomainTheory.NeighbourhoodSystems
end
