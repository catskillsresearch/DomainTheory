/-ai
If every neighbourhood contained in an element is the master neighbourhood, then the element is the bottom element.

By antisymmetry. A neighbourhood of the element is the master, which is membership in the bottom element, and the bottom element lies below every element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem eq_bot_of_no_proper {x : V₀.Element} (hx : ∀ X, x.mem X → X = V₀.master) :
    x = V₀.bot :=
  le_antisymm (fun W hW => by rw [NeighborhoodSystem.mem_bot]; exact hx W hW)
    (V₀.bot_le x)

end DomainTheory.NeighbourhoodSystems.Exercise510
