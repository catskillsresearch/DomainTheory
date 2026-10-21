/-ai
The principal filter of a neighbourhood equal to the master is the bottom element.

Substituting that equality leaves the two sides identical.
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

/-- The principal filter of the master is `⊥`. -/
theorem principal_master_eq_bot {X : Set α} (hX : V₀.mem X) (hXm : X = V₀.master) :
    V₀.principal hX = V₀.bot := by
  subst hXm; rfl

end DomainTheory.NeighbourhoodSystems.Exercise510
