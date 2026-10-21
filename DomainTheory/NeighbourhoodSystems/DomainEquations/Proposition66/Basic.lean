/-ai
This file gathers and re-exports the isomorphism of Proposition 6.6 and the identity law for the composite of the two unique homomorphisms between initial algebras. Any two initial algebras for an endofunctor are isomorphic, and the isomorphism is assembled from the unique homomorphisms in the two directions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition66.initialIso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition66.comp_desc_eq_id

@[expose] public section

/-!
# Lecture VI — Proposition 6.6 (Scott 1981, PRG-19): initial algebras are uniquely isomorphic

**Proposition 6.6.** Any two initial `T`-algebras are uniquely isomorphic.

The proof is the standard diagram chase. If `A` and `B` are both initial, initiality gives unique
homomorphisms `f : A → B` and `g : B → A`. Their composites `g ∘ f : A → A` and `f ∘ g : B → B` are
homomorphisms, and by uniqueness of homomorphisms out of an initial algebra they must equal the
identity homomorphisms. Hence the underlying morphisms of `f` and `g` are mutually inverse, giving an
isomorphism `A.carrier ≅ B.carrier`. The isomorphism is *unique* in that the homomorphism `A → B`
realising it is the only one (`iso_hom_unique`).

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}


end DomainTheory.NeighbourhoodSystems
