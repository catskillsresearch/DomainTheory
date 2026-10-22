module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise720.unionMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*}


@[simp] theorem unionMap_rel {V : NeighborhoodSystem α} {A : Set (Set (Set α))} {B : Set (Set α)} :
    (unionMap V).rel A B ↔ V.PowerDomain.PDmem A ∧ V.PDmem B ∧ ∀ S ∈ A, ∀ X ∈ S, ∃ Y ∈ B, X ⊆ Y :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems
