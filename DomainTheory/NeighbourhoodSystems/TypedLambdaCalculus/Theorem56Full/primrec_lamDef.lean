/-ai
Every primitive recursive function of finitely many natural numbers is λ-definable by a very strict approximable map from the universal argument domain to N.

The argument is induction on the primitive-recursive derivation. Zero and successor are the corresponding λ-definitions, and a projection is the λ-definition of coordinate lookup. For composition, the inductive hypotheses supply λ-definitions, which the primitive-composition construction combines. For primitive recursion, the inductive hypotheses supply λ-definitions of the base and the step, which the primitive-recursion construction combines.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_get
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_primComp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_prec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)























/-- **Every `Nat.Primrec'` function is λ-definable** by a (very strict) approximable map. -/
theorem primrec_lamDef {n : ℕ} {f : List.Vector ℕ n → ℕ} (h : Nat.Primrec' f) :
    ∃ φ : ApproximableMap 𝒩 N, LamDef φ (f : List.Vector ℕ n →. ℕ) := by
  induction h with
  | zero => exact ⟨_, lamDef_zero⟩
  | succ => exact ⟨_, lamDef_succ⟩
  | get i => exact ⟨_, lamDef_get i⟩
  | comp g _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      choose φg hφg using ihg
      exact ⟨_, lamDef_primComp _ g φf hφf φg hφg⟩
  | prec _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      obtain ⟨φg, hφg⟩ := ihg
      exact ⟨_, lamDef_prec φf φg _ _ hφf hφg⟩

end DomainTheory.NeighbourhoodSystems.Theorem56Full
