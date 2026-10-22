module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.sumMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.mem_subset_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.mem_subset_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.eq_sumMaster_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.not_inj₀_subset_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.not_inj₁_subset_inj₀

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}


end DomainTheory.NeighbourhoodSystems
