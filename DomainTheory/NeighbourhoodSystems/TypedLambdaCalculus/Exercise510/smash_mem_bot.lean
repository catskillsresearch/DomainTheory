module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem smash_mem_bot {W : Set (α ⊕ β)} :
    (smash V₀ V₁).bot.mem W ↔ W = prodNbhd V₀.master V₁.master := by
  rw [NeighborhoodSystem.mem_bot, smash_master]

end DomainTheory.NeighbourhoodSystems.Exercise510
