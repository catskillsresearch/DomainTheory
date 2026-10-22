module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}


/-- **Theorem 3.12(ii) (Scott 1981, PRG-19).** `eval ∘ ⟨curry(g) ∘ p₀, p₁⟩ = g`. -/
theorem eval_comp_curry (g : ApproximableMap (prod V₀ V₁) V₂) :
    (evalMap V₁ V₂).comp (paired ((curry g).comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) = g := by
  rw [← uncurry_eq]; exact uncurry_curry g

end DomainTheory.NeighbourhoodSystems
