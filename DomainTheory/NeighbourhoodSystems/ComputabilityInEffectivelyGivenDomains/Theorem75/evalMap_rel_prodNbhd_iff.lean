/-ai
Evaluation relates a product of a function-space neighbourhood with a domain neighbourhood to a codomain neighbourhood if and only if the function-space neighbourhood is contained in the step between those two neighbourhoods.

Rewrite the two preimages of the product neighbourhood. One direction applies the evaluation relation at each member of the function-space neighbourhood. The other restores product membership and turns containment in the step back into the evaluation relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)









































































































/-- **Evaluation against a product neighbourhood.** `(F, X) eval Y ↔ F ⊆ [X, Y]`, for any
function-space neighbourhood `F` and basic neighbourhoods `X, Y`: every map in `F` relates `X` to `Y`
exactly when `F` is contained in the step set `[X, Y] = {f ∣ f X Y}`. -/
theorem evalMap_rel_prodNbhd_iff {F : Set (ApproximableMap V₀ V₁)} (hF : (funSpace V₀ V₁).mem F)
    {X : Set α} (hX : V₀.mem X) {Y : Set β} (hY : V₁.mem Y) :
    (evalMap V₀ V₁).rel (prodNbhd F X) Y ↔ F ⊆ step X Y := by
  show (prod (funSpace V₀ V₁) V₀).mem (prodNbhd F X) ∧
    (eval V₀ V₁).rel (Sum.inl ⁻¹' prodNbhd F X) (Sum.inr ⁻¹' prodNbhd F X) Y ↔ _
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  constructor
  · rintro ⟨_, _, _, _, hrel⟩ f hf; exact mem_step.mpr (hrel f hf)
  · intro hsub
    exact ⟨prod_mem_prodNbhd hF hX, hF, hX, hY, fun f hf => mem_step.mp (hsub hf)⟩

end DomainTheory.NeighbourhoodSystems
