/-ai
The equation defining the test one holds on every partial element of the sequence domain.

On the empty string both sides are bottom: the emptiness test returns bottom, and the conditional of bottom is bottom. On a false-headed string both sides are false: the emptiness test returns false, so the outer conditional takes the inner conditional, and the zero test returns true, so the inner conditional takes false. On a true-headed string both sides are true: the emptiness test returns false, the zero test returns false, and the inner conditional takes true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.condT_bot

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44


variable {β : Type*}


/-- **Exercise 4.19 (Scott 1981, PRG-19).** The same defining equation holds on every partial
element `σ⊥` — including `⊥ = []⊥` where `empty(⊥) = ⊥` forces `cond(⊥, …) = ⊥`. -/
theorem one_def_strBot (σ : Str) : oneMap.toElementMap (strBot σ) = oneDef (strBot σ) := by
  cases σ with
  | nil =>
    rw [oneDef, emptyMap_strBot, headValC_nil, condT_bot, oneMap_strBot, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      rw [oneDef, emptyMap_strBot, headValC_false, Exercise326.cond_false,
        zeroMap_strBot, headValC_false, Exercise326.cond_true, oneMap_strBot, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strBot, headValC_true, Exercise326.cond_false,
        zeroMap_strBot, headValC_true, Exercise326.cond_false, oneMap_strBot, headValC_true]

end DomainTheory.NeighbourhoodSystems.Exercise419
