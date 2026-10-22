module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive


variable {α : Type*} {V : NeighborhoodSystem α}


/-- **Exercise 7.13 (⇒, "essentially any effectively given system").** The system reconstructed from
an effectively given `V` via its `INCL` relation is domain-isomorphic to `V`. -/
theorem reconstruct_isomorphic (P : ComputablePresentation V) : reconstruct P ≅ᴰ V :=
  ⟨(reconIso P).symm⟩

end DomainTheory.NeighbourhoodSystems.Exercise713
