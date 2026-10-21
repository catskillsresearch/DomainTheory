/-ai
The Schröder–Bernstein correspondence is the equivalence obtained from Tarski's map once the first injection makes that map injective and the second injection makes it surjective.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun_injective
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbFun_surjective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

/-- **Exercise 4.24 (Scott 1981, PRG-19).** The one-one correspondence as an `Equiv A ≃ B`. -/
noncomputable def schroeder_bernstein_equiv (hf : Injective f) (hg : Injective g) : A ≃ B :=
  Equiv.ofBijective (sbFun f g) ⟨sbFun_injective hf, sbFun_surjective hg⟩

end DomainTheory.NeighbourhoodSystems.Exercise424
