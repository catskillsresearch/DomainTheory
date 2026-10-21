/-ai
An initial algebra for an endofunctor is an algebra equipped with a homomorphism into every algebra for that endofunctor and with the assertion that this homomorphism is the only one.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.TAlgebra
public import DomainTheory.NeighbourhoodSystems.DomainEquations.AlgHom

@[expose] public section

universe u v w

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

/-- **Definition 6.5 (Scott 1981, PRG-19).** A `T`-algebra `A` is *initial* iff there is a (unique)
homomorphism from `A` into every `T`-algebra. We package the homomorphism as the data `desc` and its
uniqueness as `uniq`. -/
structure IsInitial (A : TAlgebra T) where
  /-- The chosen homomorphism into any algebra `B`. -/
  desc : (B : TAlgebra T) → AlgHom A B
  /-- It is the only homomorphism `A → B`. -/
  uniq : ∀ (B : TAlgebra T) (h : AlgHom A B), h = desc B

end DomainTheory.NeighbourhoodSystems
