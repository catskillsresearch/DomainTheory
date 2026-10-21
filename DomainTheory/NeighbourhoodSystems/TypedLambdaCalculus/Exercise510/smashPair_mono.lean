/-ai
The strict pairing is monotone in both arguments.

The master neighbourhood of the smaller pairing is the master of the larger pairing, and a proper product of neighbourhoods of the smaller elements is a proper product of neighbourhoods of the larger elements by the two inequalities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The strict pairing is monotone in both arguments. -/
theorem smashPair_mono {x x' : V₀.Element} {y y' : V₁.Element} (hx : x ≤ x') (hy : y ≤ y') :
    smashPair x y ≤ smashPair x' y' := by
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨X, Y, hx X hxX, hXne, hy Y hyY, hYne, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
