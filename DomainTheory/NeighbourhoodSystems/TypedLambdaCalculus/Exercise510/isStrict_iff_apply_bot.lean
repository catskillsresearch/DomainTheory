/-ai
An approximable map is strict if and only if it sends the bottom element to the bottom element.

If it is strict, the two elements agree by extensionality. Membership in the image of the bottom element rewrites as membership in the bottom element. A neighbourhood of that image has input the master, so strictness forces the output to be the master; conversely the master output is related from the master, which belongs to the bottom element. If instead the map sends the bottom element to the bottom element and relates the master to an output, that output belongs to the image of the bottom element, and the hypothesis together with membership in the bottom element makes it the master.
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
