module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition_6_5

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}

theorem comp_desc_eq_id (hA : IsInitial A) (hB : IsInitial B) :
    (hB.desc A).comp (hA.desc B) = AlgHom.id A := by
  rw [hA.uniq A ((hB.desc A).comp (hA.desc B)), hA.uniq A (AlgHom.id A)]

def initialIso (hA : IsInitial A) (hB : IsInitial B) : Iso A.carrier B.carrier where
  hom := (hA.desc B).hom
  inv := (hB.desc A).hom
  hom_inv_id := by
    have h := comp_desc_eq_id hA hB
    have := congrArg AlgHom.hom h
    simpa using this
  inv_hom_id := by
    have h := comp_desc_eq_id hB hA
    have := congrArg AlgHom.hom h
    simpa using this

theorem iso_hom_unique (hA : IsInitial A) (h : AlgHom A B) : h = hA.desc B :=
  hA.uniq B h

end DomainTheory.NeighbourhoodSystems
