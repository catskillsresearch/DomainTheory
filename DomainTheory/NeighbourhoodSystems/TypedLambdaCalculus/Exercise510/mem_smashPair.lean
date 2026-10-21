/-ai
The smash pair of two elements contains a set of the disjoint sum exactly when that set is the product of the two master neighbourhoods, or the product of a proper neighbourhood of the first element and a proper neighbourhood of the second.

The two sides agree by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_smashPair {x : V₀.Element} {y : V₁.Element} {W : Set (α ⊕ β)} :
    (smashPair x y).mem W ↔ W = prodNbhd V₀.master V₁.master ∨
      ∃ X Y, x.mem X ∧ X ≠ V₀.master ∧ y.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise510
