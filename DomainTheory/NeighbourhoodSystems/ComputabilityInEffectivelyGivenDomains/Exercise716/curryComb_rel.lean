module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.curryIso_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.toApproxMap_principal_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}


/-- **Exercise 7.16 — `curry` written out as a relation between neighbourhoods.** The combinator
relates a neighbourhood `G` of `(𝒟₀×𝒟₁→𝒟₂)` to a neighbourhood `H` of `(𝒟₀→(𝒟₁→𝒟₂))` exactly when
`curry g ∈ H` for every `g ∈ G`. -/
theorem curryComb_rel {G : Set (ApproximableMap (prod V₀ V₁) V₂)}
    {H : Set (ApproximableMap V₀ (funSpace V₁ V₂))} :
    (curryC V₀ V₁ V₂).rel G H ↔ (funSpace (prod V₀ V₁) V₂).mem G ∧
      (funSpace V₀ (funSpace V₁ V₂)).mem H ∧ ∀ g ∈ G, curry g ∈ H := by
  constructor
  · rintro ⟨hG, hH⟩
    rw [curryIso_apply, mem_toFilter] at hH
    obtain ⟨hHmem, hcurry⟩ := hH
    refine ⟨hG, hHmem, fun g hg => ?_⟩
    have hle : toApproxMap ((funSpace (prod V₀ V₁) V₂).principal hG) ≤ g := by
      rw [ApproximableMap.le_iff]
      intro X Y hrel
      rw [toApproxMap_rel, mem_principal] at hrel
      exact hrel.2 hg
    have hcle : curry (toApproxMap ((funSpace (prod V₀ V₁) V₂).principal hG)) ≤ curry g :=
      (curryEquiv V₀ V₁ V₂).monotone hle
    exact funSpace_mem_up_closed hHmem hcurry hcle
  · rintro ⟨hG, hH, hall⟩
    refine ⟨hG, ?_⟩
    rw [curryIso_apply, mem_toFilter]
    exact ⟨hH, hall _ (toApproxMap_principal_mem hG)⟩

end DomainTheory.NeighbourhoodSystems
