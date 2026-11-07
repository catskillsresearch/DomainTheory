module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.talgebra

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

/-- Scott's Definition 6.4: a homomorphism of `T`-algebras satisfies
`h ∘ k = m ∘ T(h)`. -/
theorem definition_64 {A B : TAlgebra T} (h : AlgHom A B) :
    h.hom ⊚ A.str = B.str ⊚ T.map h.hom := h.comm

end DomainTheory.NeighbourhoodSystems
