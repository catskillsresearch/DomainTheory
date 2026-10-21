/-ai
The constant map with value the bottom element is strict.

A related output comes with a witness of membership in the bottom element, and that membership means the output is the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.IsStrict

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The constant map at `⊥` is strict. -/
theorem isStrict_constBot : IsStrict (constMap V₀ (V₁.bot)) := by
  rintro Y ⟨_, hY⟩
  rwa [NeighborhoodSystem.mem_bot] at hY

end DomainTheory.NeighbourhoodSystems.Exercise510
