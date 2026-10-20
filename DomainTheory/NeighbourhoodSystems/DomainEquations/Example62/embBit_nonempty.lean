module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62













theorem embBit_nonempty {b : Bool} {X : Set Str} (hX : X.Nonempty) : (embBit b X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨b :: w', w', rfl, hw'⟩

end Example62
end DomainTheory.NeighbourhoodSystems
