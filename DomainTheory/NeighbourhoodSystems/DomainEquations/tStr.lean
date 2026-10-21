/-ai
Applying an endofunctor to the structure map of an algebra produces the algebra whose carrier is the image of the original carrier and whose structure map is the image of the original structure map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- For an algebra `A = (D, i)`, the functor turns the structure map into a new `T`-algebra
`(T(D), T(i))`. -/
abbrev tStr (A : TAlgebra T) : TAlgebra T where
  carrier := T.obj A.carrier
  str := T.map A.str

end DomainTheory.NeighbourhoodSystems
