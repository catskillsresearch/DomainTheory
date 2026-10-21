/-ai
Lambek's lemma packages the structure map of an initial T-algebra as an isomorphism from the image of the carrier under T back to the carrier, with inverse the descent homomorphism into the algebra whose structure map is T of the original structure map. One composite is the identity by the lemma that the structure map after that descent is the identity. The other composite equals T of that identity, because the descent is a homomorphism, the two algebra structures agree, and T preserves composition and identities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tStr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.str_comp_desc

@[expose] public section

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
