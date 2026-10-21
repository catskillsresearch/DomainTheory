/-ai
If an approximable map returns bottom at a stack and the tested coordinate is bottom or a numeral, the guard at that coordinate returns bottom.

If the coordinate is bottom, the bottom lemma for the guard applies. If it is a numeral, rewrite by the application formula and substitute both hypotheses. A zero numeral makes the zero test true, and a successor makes it false. In both cases the conditional returns the inner value, which is bottom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.guard1_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.guard1_bot

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- If `φ z = ⊥` and `zⱼ` is total-or-`⊥`, the guard stays `⊥`. -/
theorem guard1_inner_bot (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (hz : component z j = N.bot ∨ ∃ k, component z j = natElem k)
    (h : φ.toElementMap z = N.bot) : (guard1 j φ).toElementMap z = N.bot := by
  rcases hz with hb | ⟨k, hk⟩
  · exact guard1_bot j φ z hb
  · rw [guard1_apply, hk, h]
    cases k with
    | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
    | succ m => rw [zeroMap_natElem_succ, Exercise326.cond_false]

end DomainTheory.NeighbourhoodSystems.Theorem56Full
