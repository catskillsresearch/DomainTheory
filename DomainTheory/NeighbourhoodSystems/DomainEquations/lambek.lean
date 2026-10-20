module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tStr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.str_comp_desc

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- **Proposition 6.7 (Lambek's lemma; Scott 1981, PRG-19).** The structure map `i : T(D) → D` of an
initial `T`-algebra is an isomorphism `T(D) ≅ D`, with inverse the descent homomorphism `j`. -/
def lambek (A : TAlgebra T) (hA : IsInitial A) : Iso (T.obj A.carrier) A.carrier where
  hom := A.str
  inv := (hA.desc (tStr A)).hom
  inv_hom_id := str_comp_desc A hA
  hom_inv_id :=
    calc (hA.desc (tStr A)).hom ⊚ A.str
        = (tStr A).str ⊚ T.map (hA.desc (tStr A)).hom := (hA.desc (tStr A)).comm
      _ = T.map A.str ⊚ T.map (hA.desc (tStr A)).hom := rfl
      _ = T.map (A.str ⊚ (hA.desc (tStr A)).hom) := (T.map_comp _ _).symm
      _ = T.map ((𝟙 A.carrier)) := by rw [str_comp_desc A hA]
      _ = (𝟙 (T.obj A.carrier)) := T.map_id _

end DomainTheory.NeighbourhoodSystems
