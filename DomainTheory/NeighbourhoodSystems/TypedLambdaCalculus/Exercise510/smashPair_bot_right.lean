/-ai
A bottom element in the right argument collapses the strict pairing to the bottom of the smash.

An element whose only neighbourhood is the master is bottom. The master case is the master, and a proper product would require the bottom element to contain a neighbourhood other than the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.eq_bot_of_no_proper

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A `⊥` right factor collapses the strict pairing to `⊥` (choice-free). -/
theorem smashPair_bot_right (x : V₀.Element) : smashPair x V₁.bot = (smash V₀ V₁).bot := by
  apply eq_bot_of_no_proper
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · rfl
  · rw [NeighborhoodSystem.mem_bot] at hyY; exact absurd hyY hYne

end DomainTheory.NeighbourhoodSystems.Exercise510
