module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.lambek

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- Scott's Proposition 6.7 (Lambek): the structure map of an initial algebra is an isomorphism. -/
theorem proposition_67 (A : TAlgebra T) (hA : IsInitial A) :
    A.str ⊚ (hA.desc (tStr A)).hom = (AlgHom.id A).hom :=
  str_comp_desc A hA

end DomainTheory.NeighbourhoodSystems
