module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable

@[expose] public section

universe w

namespace DomainTheory.NeighbourhoodSystems

/-- An object of the category of domains: a token type together with a neighbourhood system on it. -/
structure DomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system (the "domain"). -/
  sys : NeighborhoodSystem carrier

end DomainTheory.NeighbourhoodSystems
