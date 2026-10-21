/-ai
The structure map of a T-algebra is a homomorphism from the algebra whose structure map is the image of that map under T to the original algebra. Both paths of the homomorphism square are the structure map composed with its own image under T.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tStr

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- The structure map `i : T(D) → D` is itself a homomorphism `(T(D), T(i)) → (D, i)`: the square
`i ∘ T(i) = i ∘ T(i)` commutes trivially. -/
def strHom (A : TAlgebra T) : AlgHom (tStr A) A where
  hom := A.str
  comm := rfl

end DomainTheory.NeighbourhoodSystems
