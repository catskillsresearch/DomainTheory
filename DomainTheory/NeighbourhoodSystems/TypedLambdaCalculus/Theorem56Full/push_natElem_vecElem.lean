/-ai
Pushing the numeral for a in front of the argument element of a vector u yields the argument element of a cons u.

The two elements agree on every component. At coordinate 0 both sides are the numeral for a. At a later coordinate k, if k lies below the length of u then both sides are the numeral for the corresponding entry of u, and otherwise both sides are bottom.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.eq_of_component_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_push_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_push_succ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


theorem push_natElem_vecElem {n : ℕ} (a : ℕ) (u : List.Vector ℕ n) :
    (push N).toElementMap (pair (natElem a) (vecElem u)) = vecElem (a ::ᵥ u) := by
  apply eq_of_component_eq
  intro j
  cases j with
  | zero =>
    rw [component_push_zero, component_vecElem, dite_eq_left (Nat.succ_pos n)]
    exact congrArg natElem (List.Vector.get_cons_zero a u).symm
  | succ k =>
    rw [component_push_succ, component_vecElem, component_vecElem]
    by_cases hk : k < n
    · rw [dite_eq_left hk, dite_eq_left (show k + 1 < n + 1 by omega)]
      exact congrArg natElem (List.Vector.get_cons_succ a u ⟨k, hk⟩).symm
    · rw [dite_eq_right hk, dite_eq_right (show ¬ k + 1 < n + 1 by omega)]

end DomainTheory.NeighbourhoodSystems.Theorem56Full
