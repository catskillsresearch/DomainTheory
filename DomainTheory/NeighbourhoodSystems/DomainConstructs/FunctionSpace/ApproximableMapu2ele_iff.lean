module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem ApproximableMap.le_iff {f g : ApproximableMap V₀ V₁} :
    f ≤ g ↔ ∀ X Y, f.rel X Y → g.rel X Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
