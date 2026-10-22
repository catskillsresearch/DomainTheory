module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_of_inner
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findMap_vecElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.searchMap_climb
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.searchMap_diverge

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


/-- **Minimisation** (`Nat.Partrec'.rfind` shape). Given a (very strict) realiser of a total
`f : Vector ℕ (n+1) → ℕ`, `strictGuardN n (findMap φf)` λ-defines
`v ↦ μk. f(k ::ᵥ v) = 0`. -/
theorem lamDef_rfind {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) :
    LamDef (strictGuardN n (findMap φf))
      (fun v : List.Vector ℕ n => Nat.rfind (rfindZeroPred f v)) := by
  refine lamDef_of_inner (findMap φf) _ ?_ ?_
  · intro v c hc
    rw [findMap_vecElem]
    have hc' : c ∈ Nat.rfind (rfindZeroPred f v) := hc
    rw [Nat.mem_rfind] at hc'
    obtain ⟨hcs, hcm⟩ := hc'
    have h0 : f (c ::ᵥ v) = 0 := of_decide_eq_true (Part.mem_some_iff.mp hcs).symm
    have hmin : ∀ i, i < c → f (i ::ᵥ v) ≠ 0 :=
      fun i hi => of_decide_eq_false (Part.mem_some_iff.mp (hcm hi)).symm
    exact searchMap_climb φf hf v c h0 hmin c 0 (by omega)
  · intro v hv
    rw [findMap_vecElem]
    have hdiv : ∀ k, f (k ::ᵥ v) ≠ 0 := by
      intro k h0
      refine hv ?_
      have hdom : (Nat.rfind (rfindZeroPred f v)).Dom := by
        rw [Nat.rfind_dom]
        refine ⟨k, ?_, fun {m} _ => trivial⟩
        change true ∈ Part.some (decide (f (k ::ᵥ v) = 0))
        rw [Part.mem_some_iff]
        exact (decide_eq_true_iff.mpr h0).symm
      exact hdom
    exact searchMap_diverge φf hf v hdiv 0

end Rfind
end DomainTheory.NeighbourhoodSystems.Theorem56Full
