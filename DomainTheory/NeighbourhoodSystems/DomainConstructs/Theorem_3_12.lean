module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_11

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
section
variable {V₂ : NeighborhoodSystem γ}
/- concordance: source L1327 THEOREM 3.12 currying -/
/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry(g) : 𝒟₀ → (𝒟₁ → 𝒟₂)`, where
`X curry(g) W ↔ (the X-section of g) ∈ W` (for `W = [Y, Z]` this is `X ∪ Y g Z`). -/
def curry (g : ApproximableMap (prod V₀ V₁) V₂) : ApproximableMap V₀ (funSpace V₁ V₂) where
  rel X W := ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨_, hW, _⟩ => hW
  master_rel := ⟨V₀.master_mem, (funSpace V₁ V₂).master_mem, Set.mem_univ _⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hmem⟩ ⟨_, hW', hmem'⟩
    exact ⟨hX, funSpace_mem_inter hW hW' ⟨gSection g hX, hmem, hmem'⟩,
      Set.mem_inter hmem hmem'⟩
  mono := by
    rintro X X' W W' ⟨hX, hW, hmem⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', funSpace_mem_up_closed hW' (hWW' hmem) (gSection_le hX hX' hX'X)⟩

@[simp] theorem curry_rel {g : ApproximableMap (prod V₀ V₁) V₂} {X : Set α}
    {W : Set (ApproximableMap V₁ V₂)} :
    (curry g).rel X W ↔ ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W := Iff.rfl

/-- The relational generation lemma for maps `h : 𝒟₀ → (𝒟₁ → 𝒟₂)`: `X h (⋂ᵢ [Yᵢ,Zᵢ])` iff
`X h [Yᵢ,Zᵢ]` for all `i`. -/
theorem rel_stepFun_iff (h : ApproximableMap V₀ (funSpace V₁ V₂)) {X : Set α} (hX : V₀.mem X)
    {L : List (Set β × Set γ)} (hL : ∀ p ∈ L, V₁.mem p.1 ∧ V₂.mem p.2) :
    h.rel X (stepFun L) ↔ ∀ p ∈ L, h.rel X (step p.1 p.2) := by
  induction L with
  | nil =>
    simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    show h.rel X (funSpace V₁ V₂).master
    exact h.rel_master hX
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₁.mem q.1 ∧ V₂.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (h.rel_cod hmem).2
      have hstep : h.rel X (step p.1 p.2) :=
        h.mono hmem subset_rfl Set.inter_subset_left hX (step_mem hp.1 hp.2)
      have htail : h.rel X (stepFun L) :=
        h.mono hmem subset_rfl Set.inter_subset_right hX
          ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : h.rel X (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : h.rel X (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact h.inter_right hstep htail

/-- **Theorem 3.12 (Scott 1981, PRG-19).** Uncurrying `h : 𝒟₀ → (𝒟₁ → 𝒟₂)` to `𝒟₀ × 𝒟₁ → 𝒟₂`:
`X ∪ Y (uncurry h) Z ↔ X h [Y, Z]`. -/
def uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : ApproximableMap (prod V₀ V₁) V₂ where
  rel W Z := (prod V₀ V₁).mem W ∧ h.rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z)
  rel_dom h' := h'.1
  rel_cod := by
    rintro W Z ⟨_, hrel⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    exact f.rel_cod hf
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_⟩
    rw [show (prod V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
      inl_preimage_prodNbhd, inr_preimage_prodNbhd, step_master_eq]
    exact h.master_rel
  inter_right := by
    rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    obtain ⟨f', hf'⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel')).2
    refine ⟨hW, ?_⟩
    rw [← step_inter_right (f.rel_cod hf) (f'.rel_cod hf')]
    exact h.inter_right hrel hrel'
  mono := by
    rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
    have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
    obtain ⟨A, B, hA, hB, rfl⟩ := hW₂
    rw [inl_preimage_prodNbhd] at hinl ⊢
    rw [inr_preimage_prodNbhd] at hinr ⊢
    refine ⟨prod_mem_prodNbhd hA hB, ?_⟩
    exact h.mono hrel hinl (step_subset hB hZ' hinr hZZ') hA (step_mem hB hZ')

@[simp] theorem uncurry_rel {h : ApproximableMap V₀ (funSpace V₁ V₂)}
    {W : Set (α ⊕ β)} {Z : Set γ} :
    (uncurry h).rel W Z ↔
      (prod V₀ V₁).mem W ∧ h.rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z) := Iff.rfl

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry (uncurry h) = h`. -/
theorem curry_uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : curry (uncurry h) = h := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨hX, hW, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    refine (rel_stepFun_iff h hX hL).mpr (fun p hp => ?_)
    have := hmem p hp
    -- `gSection (uncurry h) hX ∈ step p.1 p.2` means `(uncurry h).rel (prodNbhd X p.1) p.2`
    have hrel : (uncurry h).rel (prodNbhd X p.1) p.2 := this
    obtain ⟨_, hrel'⟩ := hrel
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hrel'
    exact hrel'
  · intro hrel
    have hX : V₀.mem X := h.rel_dom hrel
    have hW : (funSpace V₁ V₂).mem W := h.rel_cod hrel
    refine ⟨hX, hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    intro p hp
    show (uncurry h).rel (prodNbhd X p.1) p.2
    refine ⟨prod_mem_prodNbhd hX (hL p hp).1, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact (rel_stepFun_iff h hX hL).mp hrel p hp

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `uncurry (curry g) = g`. -/
theorem uncurry_curry (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g := by
  apply ApproximableMap.ext
  intro W Z
  constructor
  · rintro ⟨hW, _, _, hmem⟩
    rw [prodNbhd_preimage hW]; exact hmem
  · intro hrel
    have hW := g.rel_dom hrel
    refine ⟨hW, prod_mem_inl hW, step_mem (prod_mem_inr hW) (g.rel_cod hrel), ?_⟩
    show g.rel (prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W)) Z
    rwa [← prodNbhd_preimage hW]

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry` is an order-isomorphism between
`|𝒟₀ × 𝒟₁ → 𝒟₂|` and `|𝒟₀ → (𝒟₁ → 𝒟₂)|`. -/
def curryEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_rel_iff' := by
    intro g g'
    constructor
    · intro hcurry W Z hrel
      have h1 : (curry g).rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z) := by
        have hu : (uncurry (curry g)).rel W Z := by rw [uncurry_curry]; exact hrel
        exact hu.2
      have h2 := hcurry _ _ h1
      have hu' : (uncurry (curry g')).rel W Z := ⟨g.rel_dom hrel, h2⟩
      rw [uncurry_curry] at hu'
      exact hu'
    · intro hg X W hrel
      obtain ⟨hX, hW, hmem⟩ := hrel
      refine ⟨hX, hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
      intro p hp
      have hgrel : g.rel (prodNbhd X p.1) p.2 := hmem p hp
      exact hg _ _ hgrel

/-- **Theorem 3.12(i) (Scott 1981, PRG-19).** `curry(g)(x)(y) = g(x, y)`. -/
theorem toElementMap_curry_apply (g : ApproximableMap (prod V₀ V₁) V₂)
    (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨Y, hyY, X, hxX, hX, _, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
    exact ⟨Y, hyY, X, hxX, x.sub hxX, step_mem (y.sub hyY) (g.rel_cod hrel), hrel⟩

/-- `uncurry` is the composition `eval ∘ ⟨h ∘ p₀, p₁⟩`. -/
theorem uncurry_eq (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    uncurry h = (evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, evalMap_apply]
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W₀, hwW₀, hW₀, hrel⟩
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW₀
    rw [inl_preimage_prodNbhd] at hrel
    rw [inr_preimage_prodNbhd] at hrel
    obtain ⟨hwX, hwY⟩ := (prod_mem_split hX hY).mp hwW₀
    exact ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
  · rintro ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
    refine ⟨prodNbhd X Y, (prod_mem_split hX hY).mpr ⟨hwX, hwY⟩, prod_mem_prodNbhd hX hY, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact hrel

/-- **Theorem 3.12(iii) (Scott 1981, PRG-19).** `curry (eval ∘ ⟨h ∘ p₀, p₁⟩) = h`. -/
theorem curry_eval_comp (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    curry ((evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁))) = h := by
  rw [← uncurry_eq, curry_uncurry]

/-- **Theorem 3.12(ii) (Scott 1981, PRG-19).** `eval ∘ ⟨curry(g) ∘ p₀, p₁⟩ = g`. -/
theorem eval_comp_curry (g : ApproximableMap (prod V₀ V₁) V₂) :
    (evalMap V₁ V₂).comp (paired ((curry g).comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) = g := by
  rw [← uncurry_eq]; exact uncurry_curry g
end

theorem ApproximableMap.le_iff {f g : ApproximableMap V₀ V₁} :
    f ≤ g ↔ ∀ X Y, f.rel X Y → g.rel X Y := Iff.rfl

end
end DomainTheory.NeighbourhoodSystems
end
