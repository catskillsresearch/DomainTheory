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
















/-- **Theorem 3.12(iii) (Scott 1981, PRG-19).** `curry (eval ∘ ⟨h ∘ p₀, p₁⟩) = h`. -/
theorem curry_eval_comp (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    curry ((evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁))) = h := by
  rw [← uncurry_eq, curry_uncurry]

end DomainTheory.NeighbourhoodSystems
