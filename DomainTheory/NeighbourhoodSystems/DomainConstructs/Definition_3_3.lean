module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_2
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_1
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem
variable {α β γ δ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}
open ApproximableMap
/- concordance: source L1008 DEFINITION 3.3 projection mappings -/
/-- **Definition 3.3 (Scott 1981, PRG-19).** The paired mapping `⟨f, g⟩ : 𝒟₂ → 𝒟₀ × 𝒟₁`,
`Z ⟨f, g⟩ (X ∪ Y) ↔ Z f X ∧ Z g Y`. -/
def paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    ApproximableMap V₂ (prod V₀ V₁) where
  rel Z P := (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P)
  rel_dom h := f.rel_dom h.2.1
  rel_cod h := h.1
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_, ?_⟩
    · simpa using f.master_rel
    · simpa using g.master_rel
  inter_right := by
    rintro Z P P' ⟨hP, hfP, hgP⟩ ⟨hP', hfP', hgP'⟩
    have hfX := f.inter_right hfP hfP'
    have hgY := g.inter_right hgP hgP'
    refine ⟨?_, ?_, ?_⟩
    · rw [prodNbhd_preimage hP, prodNbhd_preimage hP', prodNbhd_inter]
      exact prod_mem_prodNbhd (f.rel_cod hfX) (g.rel_cod hgY)
    · rw [Set.preimage_inter]; exact hfX
    · rw [Set.preimage_inter]; exact hgY
  mono := by
    rintro Z Z₂ P P₂ ⟨_, hfP, hgP⟩ hZ₂Z hPP₂ hZ₂ hP₂
    obtain ⟨A, B, hA, hB, rfl⟩ := hP₂
    have hinl : Sum.inl ⁻¹' P ⊆ A := by
      have := Set.preimage_mono (f := Sum.inl) hPP₂; rwa [inl_preimage_prodNbhd] at this
    have hinr : Sum.inr ⁻¹' P ⊆ B := by
      have := Set.preimage_mono (f := Sum.inr) hPP₂; rwa [inr_preimage_prodNbhd] at this
    refine ⟨⟨A, B, hA, hB, rfl⟩, ?_, ?_⟩
    · rw [inl_preimage_prodNbhd]; exact f.mono hfP hZ₂Z hinl hZ₂ hA
    · rw [inr_preimage_prodNbhd]; exact g.mono hgP hZ₂Z hinr hZ₂ hB

/-- **Definition 3.3 (Scott 1981, PRG-19).** The projection `p₀ : 𝒟₀ × 𝒟₁ → 𝒟₀`,
`(X ∪ Y) p₀ X' ↔ X ⊆ X'`. -/
def proj₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) V₀ where
  rel W X' := (prod V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod V₀ V₁).master_mem, V₀.master_mem, by simp⟩
  inter_right := by
    rintro W X' X'' ⟨hW, hX', hsub⟩ ⟨_, hX'', hsub'⟩
    obtain ⟨A, B, hA, _, rfl⟩ := hW
    rw [inl_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨⟨A, B, hA, ‹_›, rfl⟩, V₀.inter_mem hX' hX'' hA (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X' X₂' ⟨_, _, hsub⟩ hW₂W hX'X₂' hW₂ hX₂'
    exact ⟨hW₂, hX₂', ((Set.preimage_mono hW₂W).trans hsub).trans hX'X₂'⟩

@[simp] theorem proj₀_rel {W : Set (α ⊕ β)} {X' : Set α} :
    (proj₀ V₀ V₁).rel W X' ↔ (prod V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X' := Iff.rfl

/-- **Definition 3.3 (Scott 1981, PRG-19).** The projection `p₁ : 𝒟₀ × 𝒟₁ → 𝒟₁`,
`(X ∪ Y) p₁ Y' ↔ Y ⊆ Y'`. -/
def proj₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) V₁ where
  rel W Y' := (prod V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod V₀ V₁).master_mem, V₁.master_mem, by simp⟩
  inter_right := by
    rintro W Y' Y'' ⟨hW, hY', hsub⟩ ⟨_, hY'', hsub'⟩
    obtain ⟨A, B, _, hB, rfl⟩ := hW
    rw [inr_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨⟨A, B, ‹_›, hB, rfl⟩, V₁.inter_mem hY' hY'' hB (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ Y' Y₂' ⟨_, _, hsub⟩ hW₂W hY'Y₂' hW₂ hY₂'
    exact ⟨hW₂, hY₂', ((Set.preimage_mono hW₂W).trans hsub).trans hY'Y₂'⟩

@[simp] theorem proj₁_rel {W : Set (α ⊕ β)} {Y' : Set β} :
    (proj₁ V₀ V₁).rel W Y' ↔ (prod V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y' := Iff.rfl

@[simp] theorem paired_rel {f : ApproximableMap V₂ V₀} {g : ApproximableMap V₂ V₁}
    {Z : Set γ} {P : Set (α ⊕ β)} :
    (paired f g).rel Z P ↔
      (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P) := Iff.rfl

@[simp] theorem toElementMap_proj₀ (z : (prod V₀ V₁).Element) :
    (proj₀ V₀ V₁).toElementMap z = z.fst := by
  apply Element.ext
  intro X'
  constructor
  · rintro ⟨W, hzW, hW, hX', hsub⟩
    obtain ⟨A, B, _, hB, rfl⟩ := hW
    rw [inl_preimage_prodNbhd] at hsub
    refine ⟨hX', z.up_mem hzW (prod_mem_prodNbhd hX' V₁.master_mem) ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨hsub, V₁.sub_master hB⟩
  · rintro ⟨hX', hz⟩
    exact ⟨prodNbhd X' V₁.master, hz, prod_mem_prodNbhd hX' V₁.master_mem, hX', by simp⟩

@[simp] theorem toElementMap_proj₁ (z : (prod V₀ V₁).Element) :
    (proj₁ V₀ V₁).toElementMap z = z.snd := by
  apply Element.ext
  intro Y'
  constructor
  · rintro ⟨W, hzW, hW, hY', hsub⟩
    obtain ⟨A, B, hA, _, rfl⟩ := hW
    rw [inr_preimage_prodNbhd] at hsub
    refine ⟨hY', z.up_mem hzW (prod_mem_prodNbhd V₀.master_mem hY') ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hA, hsub⟩
  · rintro ⟨hY', hz⟩
    exact ⟨prodNbhd V₀.master Y', hz, prod_mem_prodNbhd V₀.master_mem hY', hY', by simp⟩

theorem toElementMap_proj₀_pair (x : V₀.Element) (y : V₁.Element) :
    (proj₀ V₀ V₁).toElementMap (pair x y) = x := by
  rw [toElementMap_proj₀, fst_pair]

theorem toElementMap_proj₁_pair (x : V₀.Element) (y : V₁.Element) :
    (proj₁ V₀ V₁).toElementMap (pair x y) = y := by
  rw [toElementMap_proj₁, snd_pair]

end
end DomainTheory.NeighbourhoodSystems
end
