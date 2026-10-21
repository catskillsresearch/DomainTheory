/-ai
The composite of the unique homomorphism from an initial algebra A to an initial algebra B with the unique homomorphism from B back to A is the identity homomorphism on A.

Uniqueness of homomorphisms out of A identifies both that composite and the identity homomorphism with the unique endomorphism of A.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}

/-- Composing the two unique homomorphisms `A → B → A` gives the identity homomorphism on the initial
algebra `A`. -/
theorem comp_desc_eq_id (hA : IsInitial A) (hB : IsInitial B) :
    (hB.desc A).comp (hA.desc B) = AlgHom.id A := by
  rw [hA.uniq A ((hB.desc A).comp (hA.desc B)), hA.uniq A (AlgHom.id A)]

end DomainTheory.NeighbourhoodSystems
