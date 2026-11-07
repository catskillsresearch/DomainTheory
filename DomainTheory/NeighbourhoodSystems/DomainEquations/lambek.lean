module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition_6_5

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

abbrev tStr (A : TAlgebra T) : TAlgebra T where
  carrier := T.obj A.carrier
  str := T.map A.str

def strHom (A : TAlgebra T) : AlgHom (tStr A) A where
  hom := A.str
  comm := rfl

theorem str_comp_desc (A : TAlgebra T) (hA : IsInitial A) :
    A.str ⊚ (hA.desc (tStr A)).hom = (AlgHom.id A).hom := by
  have h : (strHom A).comp (hA.desc (tStr A)) = AlgHom.id A := by
    rw [hA.uniq A ((strHom A).comp (hA.desc (tStr A))), hA.uniq A (AlgHom.id A)]
  exact congrArg AlgHom.hom h

def lambek (A : TAlgebra T) (hA : IsInitial A) : Iso (T.obj A.carrier) A.carrier where
  hom := A.str
  inv := (hA.desc (tStr A)).hom
  inv_hom_id := str_comp_desc A hA
  hom_inv_id :=
    calc (hA.desc (tStr A)).hom ⊚ A.str
        = (tStr A).str ⊚ T.map (hA.desc (tStr A)).hom := (hA.desc (tStr A)).comm
      _ = T.map A.str ⊚ T.map (hA.desc (tStr A)).hom := rfl
      _ = T.map (A.str ⊚ (hA.desc (tStr A)).hom) := (T.map_comp _ _).symm
      _ = T.map (AlgHom.id A).hom := by rw [str_comp_desc A hA]
      _ = T.map (𝟙 A.carrier) := rfl
      _ = (𝟙 (T.obj A.carrier)) := T.map_id _

end DomainTheory.NeighbourhoodSystems
