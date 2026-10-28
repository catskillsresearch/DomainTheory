module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_18
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α β α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

def sumMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (sum V₀ V₁ h₀ h₁) (sum V₀' V₁' h₀' h₁') where
  rel W W' := (sum V₀ V₁ h₀ h₁).mem W ∧ (sum V₀' V₁' h₀' h₁').mem W' ∧
    (W' = sumMaster V₀' V₁' ∨
      (∃ X Y', W = inj₀ X ∧ W' = inj₀ Y' ∧ f.rel X Y') ∨
      (∃ Y Y', W = inj₁ Y ∧ W' = inj₁ Y' ∧ g.rel Y Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, (sum V₀' V₁' h₀' h₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨_, hW'₂, hd₂⟩

    have hmem : ∀ W'' : Set (Option (α' ⊕ β')),
        (W'' = sumMaster V₀' V₁' ∨
          (∃ X Y', W = inj₀ X ∧ W'' = inj₀ Y' ∧ f.rel X Y') ∨
          (∃ Y Y', W = inj₁ Y ∧ W'' = inj₁ Y' ∧ g.rel Y Y')) →
          (sum V₀' V₁' h₀' h₁').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hg⟩)
      · exact (sum V₀' V₁' h₀' h₁').master_mem
      · exact Or.inr (Or.inl ⟨Y', f.rel_cod hf, rfl⟩)
      · exact Or.inr (Or.inr ⟨Y', g.rel_cod hg, rfl⟩)

    have key : (W'₁ ∩ W'₂ = sumMaster V₀' V₁' ∨
        (∃ X Y', W = inj₀ X ∧ W'₁ ∩ W'₂ = inj₀ Y' ∧ f.rel X Y') ∨
        (∃ Y Y', W = inj₁ Y ∧ W'₁ ∩ W'₂ = inj₁ Y' ∧ g.rel Y Y')) := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hg₁⟩
      · rw [Set.inter_eq_right.mpr
          (show W'₂ ⊆ sumMaster V₀' V₁' from (sum V₀' V₁' h₀' h₁').sub_master hW'₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₀_subset_sumMaster (f.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hf₁⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX₁.symm.trans hWX₂)
          rw [inj₀_inter]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl, f.inter_right hf₁ hf₂⟩)
        · exact absurd ((hWX₁.symm.trans hWY₂)) (fun h =>
            not_inj₀_subset_inj₁ (h₀ X (f.rel_dom hf₁)) h.subset)
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₁_subset_sumMaster (g.rel_cod hg₁))]
          exact Or.inr (Or.inr ⟨Y, Y'₁, hWY₁, rfl, hg₁⟩)
        · exact absurd ((hWY₁.symm.trans hWX₂)) (fun h =>
            not_inj₁_subset_inj₀ (h₁ Y (g.rel_dom hg₁)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY₁.symm.trans hWY₂)
          rw [inj₁_inter]
          exact Or.inr (Or.inr ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl, g.inter_right hg₁ hg₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hf⟩ | ⟨Y, Y', rfl, rfl, hg⟩
    ·
      left; exact eq_sumMaster_of_subset hW'₂mem hW'W'₂
    ·
      obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂mem hW₂W
      have hXX₂ : X₂ ⊆ X := inj₀_subset_inj₀.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Z'₂, hZ'₂, rfl⟩
      · left; rfl
      · have hY'Y'₂ : Y' ⊆ Y'₂ := inj₀_subset_inj₀.mp hW'W'₂
        exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl,
          f.mono hf hXX₂ hY'Y'₂ hX₂ hY'₂⟩)
      · exact (not_inj₀_subset_inj₁ (h₀' Y' (f.rel_cod hf)) hW'W'₂).elim
    ·
      obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂mem hW₂W
      have hYY₂ : Y₂ ⊆ Y := inj₁_subset_inj₁.mp hW₂W
      rcases hW'₂mem with rfl | ⟨X'₂, hX'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · left; rfl
      · exact (not_inj₁_subset_inj₀ (h₁' Y' (g.rel_cod hg)) hW'W'₂).elim
      · have hY'Y'₂ : Y' ⊆ Y'₂ := inj₁_subset_inj₁.mp hW'W'₂
        exact Or.inr (Or.inr ⟨Y₂, Y'₂, rfl, rfl,
          g.mono hg hYY₂ hY'Y'₂ hY₂ hY'₂⟩)

theorem outMap₀_comp_sumMap_comp_inMap₀ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₀ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₀ (h₀ := h₀) (h₁ := h₁))) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hX, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hleft⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    ·
      rw [leftPart_sumMaster] at hleft
      have : Z = V₀'.master := Set.Subset.antisymm (V₀'.sub_master hZ) hleft
      subst this
      exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₀'.master_mem
    ·
      rw [leftPart_inj₀] at hleft
      have hXX₀ : X ⊆ X₀ := inj₀_subset_inj₀.mp (hWX₀ ▸ hinj)
      exact f.mono hf hXX₀ hleft hX hZ
    ·
      exact (not_inj₀_subset_inj₁ (h₀ X hX) (hWY₀ ▸ hinj)).elim
  · intro hf
    refine ⟨inj₀ Z, ⟨inj₀ X, ⟨f.rel_dom hf, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, f.rel_cod hf, ?_⟩
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, Z, rfl, rfl, hf⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact (leftPart_inj₀ V₀' Z).subset

theorem outMap₁_comp_sumMap_comp_inMap₁ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₁ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₁ (h₀ := h₀) (h₁ := h₁))) = g := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hY, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hright⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    · rw [rightPart_sumMaster] at hright
      have : Z = V₁'.master := Set.Subset.antisymm (V₁'.sub_master hZ) hright
      subst this
      exact g.mono g.master_rel (V₁.sub_master hY) subset_rfl hY V₁'.master_mem
    · exact (not_inj₁_subset_inj₀ (h₁ Y hY) (hWX₀ ▸ hinj)).elim
    · rw [rightPart_inj₁] at hright
      have hYY₀ : Y ⊆ Y₀ := inj₁_subset_inj₁.mp (hWY₀ ▸ hinj)
      exact g.mono hg hYY₀ hright hY hZ
  · intro hg
    refine ⟨inj₁ Z, ⟨inj₁ Y, ⟨g.rel_dom hg, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, g.rel_cod hg, ?_⟩
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, Z, rfl, rfl, hg⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact (rightPart_inj₁ V₁' Z).subset
end

section
set_option linter.unusedVariables false

theorem example_319_sum.{u_1, u_2, u_3, u_4} : And
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α' β')) α' V₀
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₀'
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) (Option (Sum α' β')) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
      f)
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α' β')) β' V₁
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₁'
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) (Option (Sum α' β')) V₁
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
      g) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α' β')) α' V₀
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₀'
        (@DomainTheory.NeighbourhoodSystems.outMap₀ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Option (Sum α β)) (Option (Sum α' β')) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
      f)
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_3} {β' : Type u_4}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    {h₀' : ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
    {h₁' : ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α' β')) β' V₁
        (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁') V₁'
        (@DomainTheory.NeighbourhoodSystems.outMap₁ α' β' V₀' V₁' h₀' h₁')
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β (Option (Sum α β)) (Option (Sum α' β')) V₁
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
          (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)
          (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
      g)
  @DomainTheory.NeighbourhoodSystems.outMap₀_comp_sumMap_comp_inMap₀
  @DomainTheory.NeighbourhoodSystems.outMap₁_comp_sumMap_comp_inMap₁
end

section
open NeighborhoodSystem ApproximableMap
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

def prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (prod V₀ V₁) (prod V₀' V₁') :=
  paired (f.comp (proj₀ V₀ V₁)) (g.comp (proj₁ V₀ V₁))

theorem toElementMap_prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (w : (prod V₀ V₁).Element) :
    (prodMap f g).toElementMap w = pair (f.toElementMap w.fst) (g.toElementMap w.snd) := by
  rw [prodMap, toElementMap_paired, toElementMap_comp, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁]

theorem toElementMap_prodMap_pair (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (x : V₀.Element) (y : V₁.Element) :
    (prodMap f g).toElementMap (pair x y) = pair (f.toElementMap x) (g.toElementMap y) := by
  rw [toElementMap_prodMap, fst_pair, snd_pair]
end

section
set_option linter.unusedVariables false

theorem example_319.{u_1, u_2, u_4, u_5} : And
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g y)))
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (w :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g) w)
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.fst α β V₀ V₁ w))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.snd α β V₀ V₁ w)))) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g y)))
  (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
    {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
    {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀')
    (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁')
    (w :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g) w)
      (@DomainTheory.NeighbourhoodSystems.pair α' β' V₀' V₁'
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α' V₀ V₀' f
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.fst α β V₀ V₁ w))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β' V₁ V₁' g
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.snd α β V₀ V₁ w))))
  @DomainTheory.NeighbourhoodSystems.toElementMap_prodMap_pair @DomainTheory.NeighbourhoodSystems.toElementMap_prodMap
end
end DomainTheory.NeighbourhoodSystems
end
