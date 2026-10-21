/-ai
A T-algebra is an object of the underlying category together with a structure map from the image of that object under the endofunctor T to the object itself.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor

@[expose] public section

universe u v w

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

/-- **Definition 6.4 (Scott 1981, PRG-19).** A *`T`-algebra*: a domain `carrier` together with a
structure map `str : T(carrier) → carrier`. -/
structure TAlgebra (T : Endofunctor Obj) where
  /-- The underlying object `E`. -/
  carrier : Obj
  /-- The structure map `k : T(E) → E`. -/
  str : ((T.obj carrier) ⟶ carrier)

end DomainTheory.NeighbourhoodSystems
