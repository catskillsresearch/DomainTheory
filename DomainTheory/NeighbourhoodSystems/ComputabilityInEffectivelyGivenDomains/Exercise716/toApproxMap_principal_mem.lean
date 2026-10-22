module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}


/-- The least map of a function-space neighbourhood `G` — `toApproxMap ↑G` — belongs to `G`. -/
theorem toApproxMap_principal_mem {G : Set (ApproximableMap V₀ V₁)}
    (hG : (funSpace V₀ V₁).mem G) : toApproxMap ((funSpace V₀ V₁).principal hG) ∈ G := by
  obtain ⟨L, hL, rfl⟩ := hG.1
  intro p hp
  show (toApproxMap ((funSpace V₀ V₁).principal hG)).rel p.1 p.2
  rw [toApproxMap_rel, mem_principal]
  exact ⟨step_mem (hL p hp).1 (hL p hp).2, fun f hf => hf p hp⟩

end DomainTheory.NeighbourhoodSystems
