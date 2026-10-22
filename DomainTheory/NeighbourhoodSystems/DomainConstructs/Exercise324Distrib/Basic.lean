module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copairProj
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.distribMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.prod_mem_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


end DomainTheory.NeighbourhoodSystems
