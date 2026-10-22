module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Decode a natural code as an integer: `pair a b ↦ a - b`. -/
def decodeInt (c : ℕ) : ℤ := (c.unpair.1 : ℤ) - (c.unpair.2 : ℤ)

end DomainTheory.NeighbourhoodSystems
