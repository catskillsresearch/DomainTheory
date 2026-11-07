module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.initialIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- Scott's Proposition 6.6: the homomorphism from an initial algebra is unique. -/
theorem proposition_66 :
    ∀ {Obj : Type*} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}
      (hA : IsInitial A) (h : AlgHom A B), h = hA.desc B :=
  @iso_hom_unique

end DomainTheory.NeighbourhoodSystems
