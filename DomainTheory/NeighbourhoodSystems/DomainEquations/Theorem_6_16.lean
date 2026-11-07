module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.minimalInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.strictDomainObj
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.seqNegMerge
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.smashProduct

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

universe w

/-- Scott's Theorem 6.16: the initial algebra embeds in any carrier with a coalgebra isomorphism. -/
theorem theorem_616 (T : Endofunctor DomainObj.{w}) (hT : ContinuousOnMaps T) (Dalg : TAlgebra T)
    (hinit : IsInitial Dalg) (E : DomainObj.{w}) (isoE : Iso (T.obj E) E) :
    Dalg.carrier.sys ⊴ E.sys :=
  trianglelefteq_of_isInitial T hT Dalg hinit E isoE

open SeqEqC

theorem sum3_nonempty {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
    {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty} :
    ∀ W, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (h₀ X hX)
  · exact j1_nonempty (h₁ Y hY)
  · exact j2_nonempty (h₂ Z hZ)

abbrev tcObj (D : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := Option (Unit ⊕ D.carrier ⊕ D.carrier)
  sys := sum3 unitSys D.sys D.sys SeqEqC.unitSys_nonempty D.nonempty D.nonempty
  nonempty := sum3_nonempty

@[simp] theorem tcObj_sys (D : StrictDomainObj.{w}) :
    (tcObj D).sys = sum3 unitSys D.sys D.sys SeqEqC.unitSys_nonempty D.nonempty D.nonempty := rfl

section ShapeLemmas

open SeqEqC

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

theorem mem_subset_j0_inv {W : Set (Option (α ⊕ β ⊕ γ))} {X : Set α}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j0 X) :
    ∃ X₂, V₀.mem X₂ ∧ W = j0 X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j0
  · exact ⟨X₂, hX₂, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
  · obtain ⟨c, hc⟩ := h₂ Z₂ hZ₂; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0

theorem mem_subset_j1_inv {W : Set (Option (α ⊕ β ⊕ γ))} {Y : Set β}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j1 Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ W = j1 Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j1
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
  · exact ⟨Y₂, hY₂, rfl⟩
  · obtain ⟨c, hc⟩ := h₂ Z₂ hZ₂; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1

theorem mem_subset_j2_inv {W : Set (Option (α ⊕ β ⊕ γ))} {Z : Set γ}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j2 Z) :
    ∃ Z₂, V₂.mem Z₂ ∧ W = j2 Z₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · exact ⟨Z₂, hZ₂, rfl⟩

end ShapeLemmas

section SumInj

open SeqEqC

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

def sinj0 (x₀ : V₀.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ X, V₀.mem X ∧ W = j0 X ∧ x₀.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [master3_inter_j0 hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, master3_inter_j0 hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x₀.sub (x₀.inter_mem hx hx'), j0_inter_j0 X X', x₀.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X', hX', rfl, x₀.up_mem hx hX' (j0_subset_j0.mp hsub)⟩
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2

@[simp] theorem sinj0_mem_j0 {x₀ : V₀.Element} {X : Set α} (hX : V₀.mem X) :
    (sinj0 (V₁ := V₁) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₀).mem (j0 X) ↔ x₀.mem X := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j0
    · rw [j0_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨X, hX, rfl, hx⟩

def sinj1 (x₁ : V₁.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ Y, V₁.mem Y ∧ W = j1 Y ∧ x₁.mem Y
  sub := by
    rintro W (rfl | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨Y, hY, rfl, hx⟩) (rfl | ⟨Y', hY', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨Y', hY', by rw [master3_inter_j1 hY'], hx'⟩
    · exact Or.inr ⟨Y, hY, by rw [Set.inter_comm, master3_inter_j1 hY], hx⟩
    · exact Or.inr ⟨Y ∩ Y', x₁.sub (x₁.inter_mem hx hx'), j1_inter_j1 Y Y', x₁.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨Y, hY, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁ Y (x₁.sub hx); exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr ⟨Y', hY', rfl, x₁.up_mem hx hY' (j1_subset_j1.mp hsub)⟩
      · obtain ⟨b, hb⟩ := h₁ Y (x₁.sub hx); exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2

@[simp] theorem sinj1_mem_j1 {x₁ : V₁.Element} {Y : Set β} (hY : V₁.mem Y) :
    (sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₁).mem (j1 Y) ↔ x₁.mem Y := by
  constructor
  · rintro (h0 | ⟨Y', hY', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · rw [j1_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Y, hY, rfl, hx⟩

def sinj2 (x₂ : V₂.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ Z, V₂.mem Z ∧ W = j2 Z ∧ x₂.mem Z
  sub := by
    rintro W (rfl | ⟨Z, hZ, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr ⟨Z, hZ, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) (rfl | ⟨Z', hZ', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨Z', hZ', by rw [master3_inter_j2 hZ'], hx'⟩
    · exact Or.inr ⟨Z, hZ, by rw [Set.inter_comm, master3_inter_j2 hZ], hx⟩
    · exact Or.inr ⟨Z ∩ Z', x₂.sub (x₂.inter_mem hx hx'), j2_inter_j2 Z Z', x₂.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr ⟨Z', hZ', rfl, x₂.up_mem hx hZ' (j2_subset_j2.mp hsub)⟩

@[simp] theorem sinj2_mem_j2 {x₂ : V₂.Element} {Z : Set γ} (hZ : V₂.mem Z) :
    (sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₂).mem (j2 Z) ↔ x₂.mem Z := by
  constructor
  · rintro (h0 | ⟨Z', hZ', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
    · rw [j2_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Z, hZ, rfl, hx⟩

end SumInj

section SumInjMap

open SeqEqC

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

theorem sinj1_mono {x x' : V₁.Element} (hx : x ≤ x') :
    sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x ≤ sinj1 x' := by
  rintro W (rfl | ⟨Y, hY, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨Y, hY, rfl, hx Y hm⟩

theorem sinj2_mono {x x' : V₂.Element} (hx : x ≤ x') :
    sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x ≤ sinj2 x' := by
  rintro W (rfl | ⟨Z, hZ, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨Z, hZ, rfl, hx Z hm⟩

end SumInjMap

section SumMap3

open SeqEqC

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

def sumMap3 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') :
    ApproximableMap (sum3 V₀ V₁ V₂ h₀ h₁ h₂) (sum3 V₀' V₁' V₂' h₀' h₁' h₂') where
  rel W W' := (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W ∧ (sum3 V₀' V₁' V₂' h₀' h₁' h₂').mem W' ∧
    (W' = master3 V₀' V₁' V₂' ∨
      (∃ X Y', W = j0 X ∧ W' = j0 Y' ∧ f₀.rel X Y') ∨
      (∃ X Y', W = j1 X ∧ W' = j1 Y' ∧ f₁.rel X Y') ∨
      (∃ X Y', W = j2 X ∧ W' = j2 Y' ∧ f₂.rel X Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem, (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem,
    Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨_, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (Option (α' ⊕ β' ⊕ γ')),
        (W'' = master3 V₀' V₁' V₂' ∨
          (∃ X Y', W = j0 X ∧ W'' = j0 Y' ∧ f₀.rel X Y') ∨
          (∃ X Y', W = j1 X ∧ W'' = j1 Y' ∧ f₁.rel X Y') ∨
          (∃ X Y', W = j2 X ∧ W'' = j2 Y' ∧ f₂.rel X Y')) →
          (sum3 V₀' V₁' V₂' h₀' h₁' h₂').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hf⟩)
      · exact (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem
      · exact Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩))
    have key : (W'₁ ∩ W'₂ = master3 V₀' V₁' V₂' ∨
        (∃ X Y', W = j0 X ∧ W'₁ ∩ W'₂ = j0 Y' ∧ f₀.rel X Y') ∨
        (∃ X Y', W = j1 X ∧ W'₁ ∩ W'₂ = j1 Y' ∧ f₁.rel X Y') ∨
        (∃ X Y', W = j2 X ∧ W'₁ ∩ W'₂ = j2 Y' ∧ f₂.rel X Y')) := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hf₁⟩
        | ⟨Z, Y'₁, hWZ₁, rfl, hf₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ master3 V₀' V₁' V₂' from
          (sum3 V₀' V₁' V₂' h₀' h₁' h₂').sub_master hW'₂)]; exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j0_subset_master3 (f₀.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hf₁⟩)
        · obtain rfl : X = X' := j0_injective (hWX₁.symm.trans hWX₂)
          rw [j0_inter_j0]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl, f₀.inter_right hf₁ hf₂⟩)
        · obtain ⟨a, ha⟩ := h₀ X (f₀.rel_dom hf₁)
          exact absurd ((hWX₁.symm.trans hWY₂) ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
        · obtain ⟨a, ha⟩ := h₀ X (f₀.rel_dom hf₁)
          exact absurd ((hWX₁.symm.trans hWZ₂) ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j1_subset_master3 (f₁.rel_cod hf₁))]
          exact Or.inr (Or.inr (Or.inl ⟨Y, Y'₁, hWY₁, rfl, hf₁⟩))
        · obtain ⟨b, hb⟩ := h₁ Y (f₁.rel_dom hf₁)
          exact absurd ((hWY₁.symm.trans hWX₂) ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
        · obtain rfl : Y = Y' := j1_injective (hWY₁.symm.trans hWY₂)
          rw [j1_inter_j1]
          exact Or.inr (Or.inr (Or.inl ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl, f₁.inter_right hf₁ hf₂⟩))
        · obtain ⟨b, hb⟩ := h₁ Y (f₁.rel_dom hf₁)
          exact absurd ((hWY₁.symm.trans hWZ₂) ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j2_subset_master3 (f₂.rel_cod hf₁))]
          exact Or.inr (Or.inr (Or.inr ⟨Z, Y'₁, hWZ₁, rfl, hf₁⟩))
        · obtain ⟨c, hc⟩ := h₂ Z (f₂.rel_dom hf₁)
          exact absurd ((hWZ₁.symm.trans hWX₂) ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
        · obtain ⟨c, hc⟩ := h₂ Z (f₂.rel_dom hf₁)
          exact absurd ((hWZ₁.symm.trans hWY₂) ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
        · obtain rfl : Z = Z' := j2_injective (hWZ₁.symm.trans hWZ₂)
          rw [j2_inter_j2]
          exact Or.inr (Or.inr (Or.inr ⟨Z, Y'₁ ∩ Y'₂, hWZ₁, rfl, f₂.inter_right hf₁ hf₂⟩))
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hf⟩ | ⟨Y, Y', rfl, rfl, hf⟩ | ⟨Z, Y', rfl, rfl, hf⟩
    · exact Or.inl (eq_master3_of_subset hW'W'₂ ((sum3 V₀' V₁' V₂' h₀' h₁' h₂').sub_master hW'₂mem))
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_j0_inv hW₂mem hW₂W
      have hX₂X : X₂ ⊆ X := j0_subset_j0.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl,
          f₀.mono hf hX₂X (j0_subset_j0.mp hW'W'₂) hX₂ hY'₂⟩)
      · obtain ⟨a, ha⟩ := h₀' Y' (f₀.rel_cod hf)
        exact absurd (hW'W'₂ (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀' Y' (f₀.rel_cod hf)
        exact absurd (hW'W'₂ (t0_mem_j0.mpr ha)) t0_not_mem_j2
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_j1_inv hW₂mem hW₂W
      have hY₂Y : Y₂ ⊆ Y := j1_subset_j1.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁' Y' (f₁.rel_cod hf)
        exact absurd (hW'W'₂ (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr (Or.inr (Or.inl ⟨Y₂, Y'₂, rfl, rfl,
          f₁.mono hf hY₂Y (j1_subset_j1.mp hW'W'₂) hY₂ hY'₂⟩))
      · obtain ⟨b, hb⟩ := h₁' Y' (f₁.rel_cod hf)
        exact absurd (hW'W'₂ (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · obtain ⟨Z₂, hZ₂, rfl⟩ := mem_subset_j2_inv hW₂mem hW₂W
      have hZ₂Z : Z₂ ⊆ Z := j2_subset_j2.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂' Y' (f₂.rel_cod hf)
        exact absurd (hW'W'₂ (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂' Y' (f₂.rel_cod hf)
        exact absurd (hW'W'₂ (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr (Or.inr (Or.inr ⟨Z₂, Y'₂, rfl, rfl,
          f₂.mono hf hZ₂Z (j2_subset_j2.mp hW'W'₂) hZ₂ hY'₂⟩))

theorem isStrict_sumMap3 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') :
    IsStrict (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂')
      f₀ f₁ f₂) := by
  rintro Y ⟨-, -, hd⟩
  have h0 : (none : Option (α ⊕ β ⊕ γ)) ∈ (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master := none_mem_master3
  rcases hd with rfl | ⟨X, Y', hWX, -, -⟩ | ⟨X, Y', hWX, -, -⟩ | ⟨X, Y', hWX, -, -⟩
  · rfl
  · exact absurd (hWX ▸ h0) none_not_mem_j0
  · exact absurd (hWX ▸ h0) none_not_mem_j1
  · exact absurd (hWX ▸ h0) none_not_mem_j2

theorem sumMap3_comp {α'' β'' γ'' : Type*} {V₀'' : NeighborhoodSystem α''}
    {V₁'' : NeighborhoodSystem β''} {V₂'' : NeighborhoodSystem γ''}
    {h₀'' : ∀ X, V₀''.mem X → X.Nonempty} {h₁'' : ∀ Y, V₁''.mem Y → Y.Nonempty}
    {h₂'' : ∀ Z, V₂''.mem Z → Z.Nonempty}
    (g₀ : ApproximableMap V₀' V₀'') (g₁ : ApproximableMap V₁' V₁'') (g₂ : ApproximableMap V₂' V₂'')
    (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁') (f₂ : ApproximableMap V₂ V₂') :
    sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀'') (h₁' := h₁'') (h₂' := h₂'')
        (g₀.comp f₀) (g₁.comp f₁) (g₂.comp f₂)
      = (sumMap3 (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (h₀' := h₀'') (h₁' := h₁'') (h₂' := h₂'')
          g₀ g₁ g₂).comp
        (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂')
          f₀ f₁ f₂) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨hW, hW'', hd⟩
    rcases hd with rfl | ⟨X, Z'', rfl, rfl, Y', hf, hg⟩ | ⟨Y, Z'', rfl, rfl, Y', hf, hg⟩
      | ⟨Z, Z'', rfl, rfl, Y', hf, hg⟩
    · exact ⟨master3 V₀' V₁' V₂', ⟨hW, (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, hW'', Or.inl rfl⟩
    · exact ⟨j0 Y', ⟨hW, Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩),
        Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩)⟩,
        Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩), hW'', Or.inr (Or.inl ⟨Y', Z'', rfl, rfl, hg⟩)⟩
    · exact ⟨j1 Y', ⟨hW, Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)),
        Or.inr (Or.inr (Or.inl ⟨Y, Y', rfl, rfl, hf⟩))⟩,
        Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)), hW'',
        Or.inr (Or.inr (Or.inl ⟨Y', Z'', rfl, rfl, hg⟩))⟩
    · exact ⟨j2 Y', ⟨hW, Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)),
        Or.inr (Or.inr (Or.inr ⟨Z, Y', rfl, rfl, hf⟩))⟩,
        Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)), hW'',
        Or.inr (Or.inr (Or.inr ⟨Y', Z'', rfl, rfl, hg⟩))⟩
  · rintro ⟨W', ⟨hW, hW', hdf⟩, _, hW'', hdg⟩
    refine ⟨hW, hW'', ?_⟩
    rcases hdg with rfl | ⟨X', Z'', hW'X', rfl, hg⟩ | ⟨Y', Z'', hW'Y', rfl, hg⟩
      | ⟨Z', Z'', hW'Z', rfl, hg⟩
    · exact Or.inl rfl
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'X'.symm) ▸ none_mem_master3) none_not_mem_j0
      · obtain rfl : Y'₀ = X' := j0_injective (hW'eq.symm.trans hW'X')
        exact Or.inr (Or.inl ⟨X, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩)
      · obtain ⟨b, hb⟩ := h₁' Y'₀ (f₁.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'X') ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂' Y'₀ (f₂.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'X') ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Y'.symm) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀' Y'₀ (f₀.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Y') ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
      · obtain rfl : Y'₀ = Y' := j1_injective (hW'eq.symm.trans hW'Y')
        exact Or.inr (Or.inr (Or.inl ⟨Y, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩))
      · obtain ⟨c, hc⟩ := h₂' Y'₀ (f₂.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Y') ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Z'.symm) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨a, ha⟩ := h₀' Y'₀ (f₀.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Z') ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
      · obtain ⟨b, hb⟩ := h₁' Y'₀ (f₁.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Z') ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
      · obtain rfl : Y'₀ = Z' := j2_injective (hW'eq.symm.trans hW'Z')
        exact Or.inr (Or.inr (Or.inr ⟨Z, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩))

theorem sumMap3_id :
    sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀) (h₁' := h₁) (h₂' := h₂)
      (idMap V₀) (idMap V₁) (idMap V₂) = idMap (sum3 V₀ V₁ V₂ h₀ h₁ h₂) := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨hW, hW', hd⟩
    refine ⟨hW, hW', ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, _, _, hXY⟩ | ⟨Y, Y', rfl, rfl, _, _, hXY⟩
      | ⟨Z, Y', rfl, rfl, _, _, hXY⟩
    · exact (sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW
    · exact j0_subset_j0.mpr hXY
    · exact j1_subset_j1.mpr hXY
    · exact j2_subset_j2.mpr hXY
  · rintro ⟨hW, hW', hsub⟩
    refine ⟨hW, hW', ?_⟩
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩
    · left; exact eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW')
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, X', rfl, rfl, hX, hX', j0_subset_j0.mp hsub⟩)
      · obtain ⟨a, ha⟩ := h₀ X hX; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X hX; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁ Y hY; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr (Or.inr (Or.inl ⟨Y, Y', rfl, rfl, hY, hY', j1_subset_j1.mp hsub⟩))
      · obtain ⟨b, hb⟩ := h₁ Y hY; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂ Z hZ; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z hZ; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr (Or.inr (Or.inr ⟨Z, Z', rfl, rfl, hZ, hZ', j2_subset_j2.mp hsub⟩))

end SumMap3

section SumInjMap

open SeqEqC

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

theorem sumMap3_sinj0 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₀ : V₀.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj0 (V₁ := V₁) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₀)
      = sinj0 (V₁ := V₁') (V₂ := V₂') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₀.toElementMap x₀) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · have hXX : X = X₀ := j0_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₀.rel_cod hf, rfl, ⟨X₀, hx, hXX ▸ hf⟩⟩
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X₀ hX₀; exact absurd ((hUeq.symm.trans hUj) ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨a, ha⟩ := h₀ X₀ hX₀; exact absurd ((hUeq.symm.trans hUj) ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j0 X, Or.inr ⟨X, x₀.sub hx, rfl, hx⟩, Or.inr (Or.inl ⟨X, x₀.sub hx, rfl⟩),
        Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩), Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩)⟩

theorem sumMap3_sinj1 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₁ : V₁.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₁)
      = sinj1 (V₀ := V₀') (V₂ := V₂') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₁.toElementMap x₁) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · obtain ⟨b, hb⟩ := h₁ Y₀ hY₀; exact absurd ((hUeq.symm.trans hUj) ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · have hXX : X = Y₀ := j1_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₁.rel_cod hf, rfl, ⟨Y₀, hx, hXX ▸ hf⟩⟩
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨b, hb⟩ := h₁ Y₀ hY₀; exact absurd ((hUeq.symm.trans hUj) ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j1 X, Or.inr ⟨X, x₁.sub hx, rfl, hx⟩, Or.inr (Or.inr (Or.inl ⟨X, x₁.sub hx, rfl⟩)),
        Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)), Or.inr (Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩))⟩

theorem sumMap3_sinj2 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₂ : V₂.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₂)
      = sinj2 (V₀ := V₀') (V₁ := V₁') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₂.toElementMap x₂) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z₀ hZ₀; exact absurd ((hUeq.symm.trans hUj) ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨c, hc⟩ := h₂ Z₀ hZ₀; exact absurd ((hUeq.symm.trans hUj) ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · have hXX : X = Z₀ := j2_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₂.rel_cod hf, rfl, ⟨Z₀, hx, hXX ▸ hf⟩⟩
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j2 X, Or.inr ⟨X, x₂.sub hx, rfl, hx⟩, Or.inr (Or.inr (Or.inr ⟨X, x₂.sub hx, rfl⟩)),
        Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨X, Y', rfl, rfl, hf⟩))⟩

end SumInjMap

open SeqEqC in

def tcMapHom {D E : StrictDomainObj.{w}} (f : (D ⟶ E)) :
    ((tcObj D) ⟶ (tcObj E)) :=
  ⟨sumMap3 (h₀ := SeqEqC.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := SeqEqC.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (idMap unitSys) f.1 f.1, isStrict_sumMap3 _ _ _⟩

end DomainTheory.NeighbourhoodSystems
