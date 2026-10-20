module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_comp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.primrec_lamDef
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_rfind

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


























/-- **Theorem 5.6 (Scott 1981, PRG-19) — every partial recursive function is λ-definable.** For each
`Nat.Partrec'` function `f : Vector ℕ n →. ℕ` there is an approximable map `φ : 𝒩 → N` that is a
*very strict* λ-definition of `f`: it returns `f`'s value on total arguments, `⊥` where `f` is
undefined, and `⊥` on any arg-like input with a `⊥` among its first `n` coordinates. -/
theorem partrec_lamDef {n : ℕ} {f : List.Vector ℕ n →. ℕ} (h : Nat.Partrec' f) :
    ∃ φ : ApproximableMap 𝒩 N, LamDef φ f := by
  induction h with
  | prim hp => exact primrec_lamDef hp
  | comp g _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      choose φg hφg using ihg
      exact ⟨_, lamDef_comp _ g φf hφf φg hφg⟩
  | rfind _ ih =>
      obtain ⟨φf, hφf⟩ := ih
      exact ⟨_, lamDef_rfind φf hφf⟩

end DomainTheory.NeighbourhoodSystems.Theorem56Full
