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

/-- Strictness is exactly `f(⊥) = ⊥`. -/
theorem isStrict_iff_apply_bot {f : ApproximableMap V₀ V₁} :
    IsStrict f ↔ f.toElementMap V₀.bot = V₁.bot := by
  constructor
  · intro h
    apply Element.ext
    intro Y
    rw [NeighborhoodSystem.mem_bot]
    constructor
    · rintro ⟨X, hX, hrel⟩
      rw [NeighborhoodSystem.mem_bot] at hX; subst hX
      exact h hrel
    · rintro rfl
      exact ⟨V₀.master, V₀.bot.master_mem, f.master_rel⟩
  · intro h Y hrel
    have : (f.toElementMap V₀.bot).mem Y := ⟨V₀.master, V₀.bot.master_mem, hrel⟩
    rw [h, NeighborhoodSystem.mem_bot] at this
    exact this

end DomainTheory.NeighbourhoodSystems.Exercise510
