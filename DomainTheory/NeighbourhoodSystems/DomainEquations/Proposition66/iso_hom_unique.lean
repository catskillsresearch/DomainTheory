/-ai
The homomorphism from an initial algebra A to an algebra B that realises their isomorphism is the only homomorphism from A to B.

It is the unique homomorphism supplied by initiality of A.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition66.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}


/-- The isomorphism of Proposition 6.6 is **unique**: the homomorphism `A → B` realising it is the
only homomorphism between the two initial algebras. -/
theorem iso_hom_unique (hA : IsInitial A) (h : AlgHom A B) : h = hA.desc B :=
  hA.uniq B h

end DomainTheory.NeighbourhoodSystems
