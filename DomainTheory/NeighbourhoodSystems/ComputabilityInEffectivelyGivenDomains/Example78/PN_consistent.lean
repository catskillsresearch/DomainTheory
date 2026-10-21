/-ai
Any two neighbourhoods of the powerset domain are consistent.

The neighbourhood indexed by the bitwise disjunction of the two indices is contained in their intersection, because that intersection equals this neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem







/-- **Any two neighbourhoods of `PN` are consistent** (Scott: "any two neighbourhoods are
consistent"): their intersection `nbhd (n ||| m)` is itself a neighbourhood contained in both. -/
theorem PN_consistent (n m : ℕ) : ∃ k, nbhd k ⊆ nbhd n ∩ nbhd m :=
  ⟨myLor n m, (nbhd_inter n m).symm.subset⟩

end DomainTheory.NeighbourhoodSystems.Example78
