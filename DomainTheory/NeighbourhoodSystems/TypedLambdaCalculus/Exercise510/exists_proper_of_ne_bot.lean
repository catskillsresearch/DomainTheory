/-ai
An element other than the bottom element contains some neighbourhood other than the master.

Suppose every neighbourhood it contains is the master. Then the element equals the bottom element, contradicting the hypothesis. One inequality is that the bottom element lies below every element. For the other, membership in the bottom element follows because a neighbourhood of the element cannot differ from the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- An element is `⊥` iff every neighbourhood it contains is the master: `x ≠ ⊥` exactly when `x`
contains a *proper* neighbourhood. -/
theorem exists_proper_of_ne_bot {x : V₀.Element} (hx : x ≠ V₀.bot) :
    ∃ X, x.mem X ∧ X ≠ V₀.master := by
  by_contra hc
  refine hx (le_antisymm (fun W hW => ?_) (V₀.bot_le x))
  rw [NeighborhoodSystem.mem_bot]
  by_contra hWne
  exact hc ⟨W, hW, hWne⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
