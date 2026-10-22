module


public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.optElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.argElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.vecElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.ArgLike
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.𝒩

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- `φ : 𝒩 → N` realises the `n`-ary partial function `f` (a *very strict* λ-definition):
`φ` returns `f`'s value on total arguments, `⊥` where `f` is undefined, and `⊥` on *any* arg-like
input with a `⊥` among its first `n` coordinates. -/
structure LamDef {n : ℕ} (φ : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ) : Prop where
  defined : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → φ.toElementMap (vecElem v) = natElem c
  undef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → φ.toElementMap (vecElem v) = N.bot
  strict : ∀ (z : 𝒩.Element), ArgLike z → ∀ i, i < n → component z i = N.bot →
    φ.toElementMap z = N.bot

end DomainTheory.NeighbourhoodSystems.Theorem56Full
