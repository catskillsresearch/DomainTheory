/-ai
For neighbourhoods X₀ and Y₀, papplyEval relates the upset of the step neighbourhood of functions sending X₀ into Y₀, the upset of X₀, and the upset of Y₀.

The three upsets are power-domain neighbourhoods. For a function neighbourhood above the step and an argument neighbourhood above X₀, the neighbourhood Y₀ is the witness: every function in the step sends X₀ into Y₀, and monotonicity of such a function carries the argument neighbourhood into Y₀.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}






/-- **Exercise 7.21 — non-triviality.** For any neighbourhoods `X₀ ∈ D`, `Y₀ ∈ E`, the set of
functions sending `X₀` into `Y₀` (the principal `ℙ(D→E)`-element `↓[X₀,Y₀]`), applied to the
argument-set `↓X₀`, covers `↓Y₀`. So `papply` does genuine work (it is not the constant map). -/
theorem papplyEval_step_witness {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {X₀ : Set α} {Y₀ : Set β} (hX₀ : V.mem X₀) (hY₀ : W.mem Y₀) :
    (papplyEval V W).rel ((funSpace V W).upSet (step X₀ Y₀)) (V.upSet X₀) (W.upSet Y₀) := by
  refine ⟨(funSpace V W).PDmem_upSet (step_mem hX₀ hY₀), V.PDmem_upSet hX₀,
    W.PDmem_upSet hY₀, ?_⟩
  intro G hG X hX
  obtain ⟨hGmem, hGsub⟩ := hG
  obtain ⟨hXmem, hXsub⟩ := hX
  refine ⟨Y₀, ⟨hY₀, subset_rfl⟩, hGmem, hXmem, hY₀, ?_⟩
  intro f hf
  have hfstep : f.rel X₀ Y₀ := mem_step.mp (hGsub hf)
  exact f.mono hfstep hXsub subset_rfl hXmem hY₀

end DomainTheory.NeighbourhoodSystems
