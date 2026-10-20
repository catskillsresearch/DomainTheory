module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- For an algebra `A = (D, i)`, the functor turns the structure map into a new `T`-algebra
`(T(D), T(i))`. -/
abbrev tStr (A : TAlgebra T) : TAlgebra T where
  carrier := T.obj A.carrier
  str := T.map A.str

end DomainTheory.NeighbourhoodSystems
