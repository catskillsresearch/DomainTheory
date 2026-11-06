module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.funSpaceEquiv
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap2
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.ProjectionMappings

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

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

def evalMap (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) V₁) V₂ := ofMap₂ (eval V₁ V₂)

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

theorem evalMap_apply (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (evalMap V₁ V₂).toElementMap (pair φ x) = (toApproxMap φ).toElementMap x := by
  rw [evalMap, ← toElementMap₂_toMap₂, toMap₂_ofMap₂, toElementMap₂_eval]

theorem toElementMap_evalMap_comp_paired (F : ApproximableMap V₀ (funSpace V₁ V₂))
    (G : ApproximableMap V₀ V₁) (w : V₀.Element) :
    ((evalMap V₁ V₂).comp (paired F G)).toElementMap w =
      (toApproxMap (F.toElementMap w)).toElementMap (G.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply]

end DomainTheory.NeighbourhoodSystems
