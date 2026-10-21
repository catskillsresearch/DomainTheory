/-ai
If two indices are consistent, then some index is a meet of them.

The value of the meet function, with the datum that it satisfies the meet condition on a consistent pair, is a witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive


namespace InclStructure

variable (I : InclStructure)



/-- **Axiom (iv).** Consistent pairs have a meet. -/
theorem axiom_iv (n m : ℕ) (h : I.CONS n m) : ∃ k, I.MEET n m k :=
  ⟨I.meetIdx n m, I.meetIdx_spec h⟩

end InclStructure
end DomainTheory.NeighbourhoodSystems.Exercise713
