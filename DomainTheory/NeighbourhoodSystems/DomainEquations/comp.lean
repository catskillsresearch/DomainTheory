/-ai
Composition of homomorphisms of T-algebras sends a homomorphism from B to C and a homomorphism from A to B to the homomorphism whose underlying morphism is the composite of the underlying morphisms. The homomorphism square holds because the squares of the two factors, functoriality of T on a composite, and associativity of composition rearrange the composite square.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.DomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.TAlgebra
public import DomainTheory.NeighbourhoodSystems.DomainEquations.AlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.IsInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Iso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63Inst2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

universe u v w

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

namespace AlgHom

/-- Composition of `T`-algebra homomorphisms (the `T`-algebras and homomorphisms form a category —
the remark after Definition 6.4). -/
def comp {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) : AlgHom A C where
  hom := β.hom ⊚ α.hom
  comm := by
    have hα := α.comm
    have hβ := β.comm
    have hmap := T.map_comp β.hom α.hom
    dsimp only [compAfter] at hα hβ hmap ⊢
    rw [← CategoryTheory.Category.assoc, hα, CategoryTheory.Category.assoc, hβ,
      ← CategoryTheory.Category.assoc, hmap]

end AlgHom

end DomainTheory.NeighbourhoodSystems
