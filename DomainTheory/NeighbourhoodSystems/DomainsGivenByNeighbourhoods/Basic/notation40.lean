/-ai
The infix symbol for domain isomorphism denotes the isomorphism of neighbourhood systems.
ai-/
module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

@[inherit_doc] infix:25 " ≅ᴰ " => Isomorphic

end DomainTheory.NeighbourhoodSystems
