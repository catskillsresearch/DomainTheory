/-ai
The structure map of an initial T-algebra, composed with the descent homomorphism into the algebra given by applying T to the structure map, is the identity on the carrier.

The composite of the structure homomorphism with that descent is a homomorphism from the algebra to itself, and so is the identity homomorphism. Initiality supplies only one such homomorphism, so the two agree, and therefore their underlying morphisms agree.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tStr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.strHom

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- The composite `i ∘ j` of `i` with the descent homomorphism `j : (D,i) → (T(D),T(i))` is the
identity on `D`. -/
theorem str_comp_desc (A : TAlgebra T) (hA : IsInitial A) :
    A.str ⊚ (hA.desc (tStr A)).hom = (𝟙 A.carrier) := by
  have h : (strHom A).comp (hA.desc (tStr A)) = AlgHom.id A := by
    rw [hA.uniq A ((strHom A).comp (hA.desc (tStr A))), hA.uniq A (AlgHom.id A)]
  exact congrArg AlgHom.hom h

end DomainTheory.NeighbourhoodSystems
