module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.mapOfSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.funIterEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.piCongrOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.funIterIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.exists_forall_swap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.toElementMap_mapOfSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.projComp_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.le_of_projComp_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 3.24(ii).** `(𝒟₀ → 𝒟₁^∞) ≅ (𝒟₀ → 𝒟₁)^∞`. -/
theorem funIter_isomorphic : funSpace V₀ (iterSys V₁) ≅ᴰ iterSys (funSpace V₀ V₁) :=
  ⟨funIterIso V₀ V₁⟩

end DomainTheory.NeighbourhoodSystems
