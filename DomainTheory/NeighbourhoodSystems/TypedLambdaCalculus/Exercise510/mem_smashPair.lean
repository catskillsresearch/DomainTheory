module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_smashPair {x : V₀.Element} {y : V₁.Element} {W : Set (α ⊕ β)} :
    (smashPair x y).mem W ↔ W = prodNbhd V₀.master V₁.master ∨
      ∃ X Y, x.mem X ∧ X ≠ V₀.master ∧ y.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise510
