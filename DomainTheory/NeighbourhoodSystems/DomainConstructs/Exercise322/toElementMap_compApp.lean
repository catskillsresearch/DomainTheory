module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- `compApp(⟨⟨g, f⟩, x⟩) = g(f(x))`. -/
theorem toElementMap_compApp (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (compApp V₀ V₁ V₂).toElementMap (pair (pair Gφ Fφ) x)
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compApp]
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end DomainTheory.NeighbourhoodSystems
