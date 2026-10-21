/-ai
If an argument is argument-like and some coordinate below n is bottom, the guard of depth n sends that argument to bottom.

Induct on n. Depth 0 is impossible, since no index is below 0. At depth m + 1, if the bottom coordinate lies strictly below m then the inner guard is already bottom and the one-coordinate guard preserves bottom; if the bottom coordinate equals m then the one-coordinate guard at m returns bottom.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.guard1_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.guard1_inner_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- If some coordinate `i < n` is `⊥` (and `z` is arg-like), the guard forces `⊥`. -/
theorem strictGuardN_strict (n : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (hz : ArgLike z) {i : ℕ} (hi : i < n) (hb : component z i = N.bot) :
    (strictGuardN n φ).toElementMap z = N.bot := by
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    rw [strictGuardN]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact guard1_inner_bot m _ z (hz m) (ih hlt)
    · exact guard1_bot m _ z (heq ▸ hb)

end DomainTheory.NeighbourhoodSystems.Theorem56Full
