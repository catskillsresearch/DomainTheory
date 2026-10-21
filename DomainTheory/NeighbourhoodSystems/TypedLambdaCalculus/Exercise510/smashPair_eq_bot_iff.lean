/-ai
The strict pairing of two elements is the bottom of the smash exactly when one of the two elements is bottom.

If the pairing is bottom and neither element is, each has a proper neighbourhood, and their product belongs to the pairing. Bottom contains only the master, so that product would be the product of the masters and a factor would be a master. If either element is bottom, an element with no proper neighbourhood is bottom: the master case is the master, and a proper product would put a non-master neighbourhood into that bottom element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.exists_proper_of_ne_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.eq_bot_of_no_proper

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The strict pairing is `⊥` iff one of the components is `⊥`: the smash glues `(⊥, y)` and `(x, ⊥)`
to a single bottom. -/
theorem smashPair_eq_bot_iff {x : V₀.Element} {y : V₁.Element} :
    smashPair x y = (smash V₀ V₁).bot ↔ x = V₀.bot ∨ y = V₁.bot := by
  constructor
  · intro h
    by_contra hcon
    obtain ⟨hx, hy⟩ := not_or.mp hcon
    obtain ⟨X, hxX, hXne⟩ := exists_proper_of_ne_bot hx
    obtain ⟨Y, hyY, hYne⟩ := exists_proper_of_ne_bot hy
    -- `prodNbhd X Y` is a proper member of `smashPair x y`, but `⊥` contains only the master.
    have hmem : (smashPair x y).mem (prodNbhd X Y) :=
      Or.inr ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩
    rw [h, smash_mem_bot] at hmem
    obtain ⟨hX, _⟩ := prodNbhd_injective hmem
    exact hXne hX
  · intro h
    apply eq_bot_of_no_proper
    rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
    · rfl
    · exfalso
      rcases h with hx | hy
      · rw [hx, NeighborhoodSystem.mem_bot] at hxX; exact hXne hxX
      · rw [hy, NeighborhoodSystem.mem_bot] at hyY; exact hYne hyY

end DomainTheory.NeighbourhoodSystems.Exercise510
