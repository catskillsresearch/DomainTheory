module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Unit.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


/-- **Any two `NeighborhoodSystem`s with `Unique` element posets determine isomorphic domains.** -/
theorem isomorphic_of_unique (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    [Unique V₀.Element] [Unique V₁.Element] : V₀ ≅ᴰ V₁ :=
  ⟨isoOfUnique V₀ V₁⟩

end DomainTheory.NeighbourhoodSystems
