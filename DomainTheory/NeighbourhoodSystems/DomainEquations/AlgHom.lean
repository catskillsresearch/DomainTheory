module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.TAlgebra

@[expose] public section

universe u v w

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

/-- **Definition 6.4 (Scott 1981, PRG-19).** A *homomorphism* of `T`-algebras `(E,k) → (F,m)`: a map
`hom : E → F` making the square commute, i.e. `hom ∘ k = m ∘ T(hom)`. -/
structure AlgHom (A B : TAlgebra T) where
  /-- The underlying morphism `h : E → F`. -/
  hom : (A.carrier ⟶ B.carrier)
  /-- The homomorphism square `h ∘ k = m ∘ T(h)`. -/
  comm : hom ⊚ A.str = B.str ⊚ T.map hom

end DomainTheory.NeighbourhoodSystems
