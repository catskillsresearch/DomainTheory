module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.guard1_total

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)













/-- On arguments whose first `n` coordinates are all total, the guard is transparent. -/
theorem strictGuardN_total (n : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (h : ∀ j, j < n → ∃ k, component z j = natElem k) :
    (strictGuardN n φ).toElementMap z = φ.toElementMap z := by
  induction n with
  | zero => rfl
  | succ m ih =>
    obtain ⟨k, hk⟩ := h m (Nat.lt_succ_self m)
    rw [strictGuardN, guard1_total m _ z hk]
    exact ih (fun j hj => h j (Nat.lt_succ_of_lt hj))

end DomainTheory.NeighbourhoodSystems.Theorem56Full
