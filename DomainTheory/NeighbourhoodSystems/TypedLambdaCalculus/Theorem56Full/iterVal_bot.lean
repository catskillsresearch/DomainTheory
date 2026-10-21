/-ai
If a realiser λ-defines a total function that never returns zero when a counter is consed onto a parameter vector, then every finite approximant of the search returns bottom at the stack of every such cons.

Induct on the approximant index, with the counter quantified. The zeroth approximant is bottom. For a successor, the value at the current counter is some positive numeral. Unfold one search step, simplify the head, the tail, and the push on the numeral stack, evaluate the realiser, and take the false branch of the conditional. The continuation is the previous approximant at the next counter, which is bottom by the inductive hypothesis.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_coe_val
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.push_natElem_vecElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.iterVal_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.iterVal_succ

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- Along a *no-zero* trace, every finite approximant returns `⊥` (induction on the approximant
index, with the counter universally quantified since the search advances it). -/
theorem iterVal_bot {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n)
    (hdiv : ∀ k, f (k ::ᵥ v) ≠ 0) :
    ∀ m k, (toApproxMap ((findOp φf).iterElem m)).toElementMap (vecElem (k ::ᵥ v)) = N.bot := by
  intro m
  induction m with
  | zero => intro k; exact iterVal_zero φf (vecElem (k ::ᵥ v))
  | succ m ih =>
    intro k
    have hne := hdiv k
    obtain ⟨j, hj⟩ : ∃ j, f (k ::ᵥ v) = j + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
    rw [← push_natElem_vecElem, iterVal_succ, Exercise511.head_push, Exercise511.tail_push,
      push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hj, zeroMap_natElem_succ,
      Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]
    exact ih (k + 1)

end Rfind
end DomainTheory.NeighbourhoodSystems.Theorem56Full
