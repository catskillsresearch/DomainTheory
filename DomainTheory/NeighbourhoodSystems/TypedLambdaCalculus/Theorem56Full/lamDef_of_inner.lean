module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.LamDef
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.guard1
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.strictGuardN
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.tupleMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.precBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.recOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.recMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.searchMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.evalAt
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.rfindZeroPred
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.oneArg
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_argElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_vecElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.strictGuardN_total
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.strictGuardN_strict
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.vecElem_totals

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- **Master constructor.** Wrapping an `inner` map (correct on total arguments) in `strictGuardN n`
yields a full, very strict λ-definition. The `strict` clause is then automatic. -/
theorem lamDef_of_inner {n : ℕ} (inner : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ)
    (hdef : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → inner.toElementMap (vecElem v) = natElem c)
    (hundef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → inner.toElementMap (vecElem v) = N.bot) :
    LamDef (strictGuardN n inner) f where
  defined v c hc := by
    rw [strictGuardN_total n inner (vecElem v) (vecElem_totals v)]; exact hdef v c hc
  undef v hv := by
    rw [strictGuardN_total n inner (vecElem v) (vecElem_totals v)]; exact hundef v hv
  strict z hz i hi hb := strictGuardN_strict n inner z hz hi hb

end DomainTheory.NeighbourhoodSystems.Theorem56Full
