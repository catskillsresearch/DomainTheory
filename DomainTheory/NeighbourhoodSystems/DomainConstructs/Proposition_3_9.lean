module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
/- concordance: source L1181 PROPOSITION 3.9 consistent step neighbourhoods -/
/-- **Proposition 3.9 (Scott 1981, PRG-19).** The least map `f₀` belongs to the neighbourhood:
`Xᵢ f₀ Yᵢ` for every `(Xᵢ, Yᵢ) ∈ L`. -/
theorem leastMap_mem_stepFun {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : leastMap L hL hcons ∈ stepFun L := by
  intro p hp
  exact ⟨(hL p hp).1, (hL p hp).2, interYs_subset_of_mem hp⟩

/-- **Theorem 3.13(ii) (Scott 1981, PRG-19).** `F` is bounded in `|𝒟₀ → 𝒟₁|` iff `{f(x) ∣ f ∈ F}` is
bounded in `|𝒟₁|` for each `x ∈ |𝒟₀|`. The forward direction is `le_iff_toElementMap_le` (3.13(i))
applied pointwise; the backward direction builds the bound `sSupMaps F`. -/
theorem mapsBounded_iff_pointwiseBounded {F : Set (ApproximableMap V₀ V₁)} :
    MapsBounded F ↔ PointwiseBounded F := by
  constructor
  · intro ⟨h, hh⟩ x
    refine ⟨h.toElementMap x, fun z hz => ?_⟩
    obtain ⟨f, hf, rfl⟩ := hz
    exact (le_iff_toElementMap_le.mp (hh f hf)) x
  · intro hpb
    refine ⟨sSupMaps F hpb, fun f hf X Y hrel => ?_⟩
    have hX : V₀.mem X := f.rel_dom hrel
    have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
    exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hpb hX) ⟨f, hf, rfl⟩) Y hmem⟩

/-- The relation `X f Y` holds for `f` in the neighbourhood `stepFun L` at the master output, and
more importantly `f` relates `X` to the whole intersection `interYs Δ₁ L X` (finite intersectivity
over the relevant outputs). The case split deciding `X ⊆ Xᵢ` is a documented classical step. -/
theorem rel_interYs {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} (hf : f ∈ stepFun L)
    {X : Set α} (hX : V₀.mem X) : f.rel X (interYs V₁.master L X) := by
  induction L with
  | nil =>
    rw [interYs_nil]
    exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem
  | cons p L ih =>
    have hftail : f ∈ stepFun L := fun q hq => hf q (List.mem_cons.mpr (Or.inr hq))
    have htail := ih hftail
    by_cases hXp : X ⊆ p.1
    · have hp : f.rel p.1 p.2 := hf p (List.mem_cons.mpr (Or.inl rfl))
      have hXp2 : f.rel X p.2 := f.mono hp hXp subset_rfl hX (f.rel_cod hp)
      have heq : interYs V₁.master (p :: L) X = p.2 ∩ interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 hXp, h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩
      rw [heq]; exact f.inter_right hXp2 htail
    · have heq : interYs V₁.master (p :: L) X = interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hXp, h⟩⟩
      rw [heq]; exact htail

/-- **Proposition 3.9 (Scott 1981, PRG-19).** `f₀` is the *minimal* element of the neighbourhood:
any `f` with `Xᵢ f Yᵢ` for all `i` satisfies `f₀ ⊆ f`. -/
theorem leastMap_le {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {f : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) : leastMap L hL hcons ≤ f := by
  rintro X Y ⟨hX, hY, hsub⟩
  exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

theorem sSupMaps_le {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {h : ApproximableMap V₀ V₁} (hh : ∀ f ∈ F, f ≤ h) : sSupMaps F hF ≤ h := by
  intro X Y hrel
  obtain ⟨hX, hYmem⟩ := hrel
  have hle : supOnPrincipal F hF X hX ≤ h.toElementMap (V₀.principal hX) :=
    V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
      obtain ⟨f, hf, rfl⟩ := hs
      exact (le_iff_toElementMap_le.mp (hh f hf)) (V₀.principal hX)
  exact (h.rel_iff_mem_principal hX).mpr (hle Y hYmem)

/-- **Remark after Proposition 3.9 (Scott 1981, PRG-19).** When the neighbourhood is consistent,
`⋂ [Xᵢ, Yᵢ] ⊆ [X, Y]` iff `⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`. This is the form used to check that `curry` is
monotone (and hence approximable). -/
theorem stepFun_subset_step_iff {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    (stepFun L : Set (ApproximableMap V₀ V₁)) ⊆ step X Y ↔ interYs V₁.master L X ⊆ Y := by
  constructor
  · intro hsub
    have := hsub (leastMap_mem_stepFun hL hcons)
    exact (mem_step.mp this).2.2
  · intro hsub f hf
    exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

section
variable {V₂ : NeighborhoodSystem γ}

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
end

theorem toElementMap_sSupMaps_principal {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {X : Set α} (hX : V₀.mem X) :
    (sSupMaps F hF).toElementMap (V₀.principal hX) = supOnPrincipal F hF X hX :=
  toElementMap_ofMono_principal _ (supOnPrincipal_mono F hF) X hX

theorem toElementMap_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    (x : V₀.Element) :
    (sSupMaps F hF).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F) (hF x) := by
  apply le_antisymm
  · -- `(⊔F)(x) ⊑ ⊔{f(x)}`: read `(⊔F)(x)` off some principal `↑X` (Ex 2.9), where the
    -- principal value `(⊔F)(↑X) = ⊔{f(↑X)}` is bounded above by `⊔{f(x)}` (monotonicity, `↑X ⊑ x`).
    intro Y hY
    rw [toElementMap_mem_iff_principal (sSupMaps F hF) x] at hY
    obtain ⟨X, hxX, hY'⟩ := hY
    have hX : V₀.mem X := x.sub hxX
    rw [toElementMap_sSupMaps_principal hF] at hY'
    have hprinc : V₀.principal hX ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    have hsub : supOnPrincipal F hF X hX ≤ V₁.sSup (Set.image (fun f => f.toElementMap x) F) (hF x) :=
      V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
        obtain ⟨f, hf, rfl⟩ := hs
        exact (toElementMap_mono f hprinc).trans (V₁.le_sSup _ (hF x) ⟨f, hf, rfl⟩)
    exact hsub Y hY'
  · -- `⊔{f(x)} ⊑ (⊔F)(x)`: `(⊔F)(x)` is an upper bound of every `f(x)` since `f ⊑ ⊔F` (3.13(i)).
    refine V₁.sSup_le _ (hF x) fun s hs => ?_
    obtain ⟨f, hf, rfl⟩ := hs
    exact le_iff_toElementMap_le.mp (le_sSupMaps hF hf) x

/-- **Theorem 3.13(iii) (Scott 1981, PRG-19).** When `F` is bounded, `(⊔F)(x) = ⊔{f(x) ∣ f ∈ F}`
(stated with the boundedness hypothesis in Scott's `MapsBounded` form). -/
theorem toElementMap_sSupMaps' {F : Set (ApproximableMap V₀ V₁)} (hF : MapsBounded F) (x : V₀.Element) :
    (sSupMaps F (mapsBounded_iff_pointwiseBounded.mp hF)).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F)
        (mapsBounded_iff_pointwiseBounded.mp hF x) :=
  toElementMap_sSupMaps (mapsBounded_iff_pointwiseBounded.mp hF) x

section
variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(f, x) = f(x)` (with the filter `φ` viewed as
the map `toApproxMap φ` via Theorem 3.10). -/
theorem toElementMap₂_eval (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (eval V₁ V₂).toElementMap₂ φ x = (toApproxMap φ).toElementMap x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨F, X, hφF, hxX, _, hX, hY, hrel⟩
    refine ⟨X, hxX, ?_⟩
    show φ.mem (step X Y)
    exact φ.up_mem hφF (step_mem hX hY) (fun f hf => hrel f hf)
  · rintro ⟨X, hxX, hrel⟩
    have hstep : (funSpace V₁ V₂).mem (step X Y) := φ.sub hrel
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hstep).2
    exact ⟨step X Y, X, hrel, hxX, hstep, f.rel_dom hf, f.rel_cod hf, fun g hg => hg⟩

/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(⟨f, x⟩) = f(x)`. -/
theorem evalMap_apply (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (evalMap V₁ V₂).toElementMap (pair φ x) = (toApproxMap φ).toElementMap x := by
  rw [evalMap, ← toElementMap₂_toMap₂, toMap₂_ofMap₂, toElementMap₂_eval]

/-- `(eval ∘ ⟨F, G⟩)(w) = F(w)(G(w))`. -/
theorem toElementMap_evalMap_comp_paired (F : ApproximableMap V₀ (funSpace V₁ V₂))
    (G : ApproximableMap V₀ V₁) (w : V₀.Element) :
    ((evalMap V₁ V₂).comp (paired F G)).toElementMap w =
      (toApproxMap (F.toElementMap w)).toElementMap (G.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply]
end

theorem toFilter_le_iff {f g : ApproximableMap V₀ V₁} : toFilter f ≤ toFilter g ↔ f ≤ g :=
  (funSpaceEquiv V₀ V₁).symm.map_rel_iff'

theorem mapsBounded_to_filters {F : Set (ApproximableMap V₀ V₁)} (h : MapsBounded F) :
    (funSpace V₀ V₁).Bounded (Set.image toFilter F) := by
  obtain ⟨h, hh⟩ := h
  refine ⟨toFilter h, fun φ hφ => ?_⟩
  obtain ⟨f, hf, rfl⟩ := hφ
  exact (toFilter_le_iff).mpr (hh f hf)

section
variable {V₂ : NeighborhoodSystem γ}

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
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise317
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- The truth domain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

/-- Tokens of `T`: `{0, 1}`. -/
abbrev Token := Example12.Token

/-- `T`-neighbourhoods are non-empty (`∅ ∉ T`). -/
theorem T_nbhd_nonempty {F : Set Token} (hF : T.mem F) : F.Nonempty := by
  rcases (Example12.mem_iff F).mp hF with rfl | rfl | rfl
  · exact ⟨0, by simp [Example12.master]⟩
  · exact ⟨0, by simp [Example12.zero]⟩
  · exact ⟨1, by simp [Example12.one]⟩

/-- The `T`-neighbourhood selected by a bit: `false ↦ {0}`, `true ↦ {1}`. -/
def bitNbhd : Bool → Set Token
  | false => Example12.zero
  | true => Example12.one

theorem bitNbhd_mem (b : Bool) : T.mem (bitNbhd b) := by
  cases b
  · exact Example12.mem_zero
  · exact Example12.mem_one

/-- `encSet σ ⊆ ℕ × {0,1}`: pin copy `i` to `bitNbhd σ[i]` for `i < |σ|`, free otherwise. -/
def encSet (σ : Str) : Set (ℕ × Token) := {p | ∀ b, σ[p.1]? = some b → p.2 ∈ bitNbhd b}

@[simp] theorem mem_encSet {σ : Str} {p : ℕ × Token} :
    p ∈ encSet σ ↔ ∀ b, σ[p.1]? = some b → p.2 ∈ bitNbhd b := Iff.rfl

@[simp] theorem encSet_nil : encSet [] = Set.univ := by
  ext p; simp [encSet]

theorem comparable_of_agree : ∀ {τ τ' : Str},
    (∀ (i : ℕ) (b b' : Bool), τ[i]? = some b → τ'[i]? = some b' → b = b') → τ <+: τ' ∨ τ' <+: τ
  | [], _, _ => Or.inl (List.nil_prefix)
  | _ :: _, [], _ => Or.inr (List.nil_prefix)
  | a :: s, a' :: s', hag => by
      have ha : a = a' := hag 0 a a' (by simp) (by simp)
      subst ha
      have hrec : ∀ (i : ℕ) (b b' : Bool), s[i]? = some b → s'[i]? = some b' → b = b' := by
        intro i b b' hb hb'
        exact hag (i + 1) b b' (by simpa using hb) (by simpa using hb')
      rcases comparable_of_agree hrec with h | h
      · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩)

/-- Two prefixes that both bound a common non-empty `T^∞`-neighbourhood agree where both defined. -/
theorem encSet_agree {τ τ' : Str} {W : Set (ℕ × Token)} (hW : (iterSys T).mem W)
    (h : W ⊆ encSet τ) (h' : W ⊆ encSet τ') {i : ℕ} {b b' : Bool}
    (hb : τ[i]? = some b) (hb' : τ'[i]? = some b') : b = b' := by
  obtain ⟨t, ht⟩ := T_nbhd_nonempty (hW.1 i)
  have h1 : t ∈ bitNbhd b := (h ht) b hb
  have h2 : t ∈ bitNbhd b' := (h' ht) b' hb'
  by_contra hne
  cases b <;> cases b' <;> simp_all [bitNbhd, Example12.zero, Example12.one]

/-- A longer prefix encodes to a *smaller* set: `σ ⪯ σ' ⟹ encSet σ' ⊆ encSet σ`. -/
theorem encSet_anti {σ σ' : Str} (h : σ <+: σ') : encSet σ' ⊆ encSet σ := by
  obtain ⟨t, rfl⟩ := h
  rintro ⟨i, x⟩ hp b hb
  have hi : i < σ.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hb; exact hlt
  exact hp b (by rw [List.getElem?_append_left hi]; exact hb)

theorem fiber_encSet_none {σ : Str} {i : ℕ} (h : σ[i]? = none) :
    fiber (encSet σ) i = Set.univ := by
  ext t
  simp only [mem_fiber, mem_encSet, Set.mem_univ, iff_true]
  intro b hb; rw [h] at hb; exact absurd hb (by simp)

theorem fiber_encSet_some {σ : Str} {i : ℕ} {b : Bool} (h : σ[i]? = some b) :
    fiber (encSet σ) i = bitNbhd b := by
  ext t
  simp only [mem_fiber, mem_encSet]
  constructor
  · intro hh; exact hh b h
  · intro ht b' hb'; rw [h] at hb'; cases hb'; exact ht

/-- `encSet σ` is a `T^∞`-neighbourhood. -/
theorem encSet_mem (σ : Str) : (iterSys T).mem (encSet σ) := by
  refine ⟨fun i => ?_, σ.length, fun i hi => ?_⟩
  · cases h : σ[i]? with
    | none => rw [fiber_encSet_none h]; exact T.master_mem
    | some b => rw [fiber_encSet_some h]; exact bitNbhd_mem b
  · rw [fiber_encSet_none (List.getElem?_eq_none_iff.mpr hi)]; rfl

/-- **The encoding map `f : B → T^∞`.** Relates the cone `σΣ*` to every `T^∞`-neighbourhood weaker
than `encSet σ`. -/
def f : ApproximableMap B (iterSys T) where
  rel X W := ∃ σ, X = cone σ ∧ (iterSys T).mem W ∧ encSet σ ⊆ W
  rel_dom := fun ⟨σ, hX, _⟩ => hX ▸ memB_cone σ
  rel_cod := fun ⟨_, _, hW, _⟩ => hW
  master_rel := ⟨[], cone_nil.symm, (iterSys T).master_mem, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro X W W' ⟨σ, hX, hWmem, hWsub⟩ ⟨σ', hX', hW'mem, hW'sub⟩
    obtain rfl : σ = σ' := cone_injective (hX.symm.trans hX')
    exact ⟨σ, hX, (iterSys T).inter_mem hWmem hW'mem (encSet_mem σ)
      (Set.subset_inter hWsub hW'sub), Set.subset_inter hWsub hW'sub⟩
  mono := by
    rintro X X' W W' ⟨σ, hX, _, hWsub⟩ hX'X hWW' hX' hW'mem
    obtain ⟨σ', rfl⟩ := hX'
    subst hX
    have hpre : σ <+: σ' := cone_subset_cone.mp hX'X
    exact ⟨σ', rfl, hW'mem, (encSet_anti hpre).trans (hWsub.trans hWW')⟩

/-- **The decoding map `g : T^∞ → B`.** Relates `W` to the cone `τΣ*` exactly when `W ⊆ encSet τ`,
i.e. `W` pins the first `|τ|` copies to `τ`. -/
def g : ApproximableMap (iterSys T) B where
  rel W X := (iterSys T).mem W ∧ ∃ τ, X = cone τ ∧ W ⊆ encSet τ
  rel_dom h := h.1
  rel_cod := fun ⟨_, τ, hX, _⟩ => hX ▸ memB_cone τ
  master_rel := ⟨(iterSys T).master_mem, [], cone_nil.symm, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro W X X' ⟨hW, τ, hX, hWτ⟩ ⟨_, τ', hX', hWτ'⟩
    subst hX; subst hX'
    rcases comparable_of_agree (fun i b b' => encSet_agree hW hWτ hWτ') with hpre | hpre
    · exact ⟨hW, τ', by rw [Set.inter_eq_right.mpr (cone_subset_cone.mpr hpre)], hWτ'⟩
    · exact ⟨hW, τ, by rw [Set.inter_eq_left.mpr (cone_subset_cone.mpr hpre)], hWτ⟩
  mono := by
    rintro W W₂ X X₂ ⟨_, τ, hX, hWτ⟩ hW₂W hXX₂ hW₂ hX₂
    obtain ⟨τ₂, rfl⟩ := hX₂
    subst hX
    have hpre : τ₂ <+: τ := cone_subset_cone.mp hXX₂
    exact ⟨hW₂, τ₂, rfl, hW₂W.trans (hWτ.trans (encSet_anti hpre))⟩

theorem exists_not_mem_bitNbhd (b : Bool) : ∃ t : Token, t ∉ bitNbhd b := by
  cases b
  · exact ⟨1, by simp [bitNbhd, Example12.zero]⟩
  · exact ⟨0, by simp [bitNbhd, Example12.one]⟩

end
end DomainTheory.NeighbourhoodSystems.Exercise317
end
