module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_10

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_5
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
section
variable {V₂ : NeighborhoodSystem γ}
/- concordance: source L1291 THEOREM 3.11 evaluation combinator -/
/-- **Theorem 3.11 (Scott 1981, PRG-19).** The two-variable evaluation map
`eval : (𝒟₁ → 𝒟₂) × 𝒟₁ → 𝒟₂`, `F, X eval Y ↔ X f Y for all f ∈ F`. -/
def eval (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap₂ (funSpace V₁ V₂) V₁ V₂ where
  rel F X Y := (funSpace V₁ V₂).mem F ∧ V₁.mem X ∧ V₂.mem Y ∧ ∀ f ∈ F, f.rel X Y
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨(funSpace V₁ V₂).master_mem, V₁.master_mem, V₂.master_mem,
    fun f _ => f.master_rel⟩
  inter_right := by
    rintro F X Y Y' ⟨hF, hX, hY, hrel⟩ ⟨_, _, hY', hrel'⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hF).2
    refine ⟨hF, hX, ?_, fun g hg => g.inter_right (hrel g hg) (hrel' g hg)⟩
    exact f.rel_cod (f.inter_right (hrel f hf) (hrel' f hf))
  mono := by
    rintro F F' X X' Y Y' ⟨hF, hX, hY, hrel⟩ hF'F hX'X hYY' hF' hX' hY'
    exact ⟨hF', hX', hY', fun f hf => f.mono (hrel f (hF'F hf)) hX'X hYY' hX' hY'⟩

/-- **Theorem 3.11 (Scott 1981, PRG-19).** Evaluation as a single approximable map out of the
product `(𝒟₁ → 𝒟₂) × 𝒟₁ → 𝒟₂`. -/
def evalMap (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) V₁) V₂ := ofMap₂ (eval V₁ V₂)

/-- The `X`-section of a two-variable map `g : 𝒟₀ × 𝒟₁ → 𝒟₂`: the map `𝒟₁ → 𝒟₂` with
`Y (gSection g X) Z ↔ X ∪ Y g Z`. -/
def gSection (g : ApproximableMap (prod V₀ V₁) V₂) {X : Set α} (hX : V₀.mem X) :
    ApproximableMap V₁ V₂ where
  rel Y Z := g.rel (prodNbhd X Y) Z
  rel_dom h := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  rel_cod h := g.rel_cod h
  master_rel := g.rel_master (prod_mem_prodNbhd hX V₁.master_mem)
  inter_right h h' := g.inter_right h h'
  mono := by
    intro Y Y' Z Z' h hY'Y hZZ' hY' hZ'
    exact g.mono h (prodNbhd_subset_iff.mpr ⟨subset_rfl, hY'Y⟩) hZZ'
      (prod_mem_prodNbhd hX hY') hZ'

@[simp] theorem gSection_rel {g : ApproximableMap (prod V₀ V₁) V₂} {X : Set α} (hX : V₀.mem X)
    {Y : Set β} {Z : Set γ} : (gSection g hX).rel Y Z ↔ g.rel (prodNbhd X Y) Z := Iff.rfl

theorem gSection_le {g : ApproximableMap (prod V₀ V₁) V₂} {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) : gSection g hX ≤ gSection g hX' := by
  intro Y Z h
  have hY := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  exact g.mono h (prodNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩) subset_rfl
    (prod_mem_prodNbhd hX' hY) (g.rel_cod h)

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

end
end DomainTheory.NeighbourhoodSystems
end
