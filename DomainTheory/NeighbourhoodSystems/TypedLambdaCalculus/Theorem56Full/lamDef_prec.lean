module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_of_inner
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.recMap_eval

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


section Prec

variable (φf φg : ApproximableMap 𝒩 N)


/-- **Primitive recursion** (`Nat.Primrec'.prec` shape). -/
theorem lamDef_prec {n : ℕ} (f₀ : List.Vector ℕ n → ℕ) (g₀ : List.Vector ℕ (n + 2) → ℕ)
    (hf : LamDef φf (f₀ : List.Vector ℕ n →. ℕ))
    (hg : LamDef φg (g₀ : List.Vector ℕ (n + 2) →. ℕ)) :
    LamDef (strictGuardN (n + 1) (recMap φf φg))
      (((fun v : List.Vector ℕ (n + 1) =>
        v.head.rec (f₀ v.tail) fun y IH => g₀ (y ::ᵥ IH ::ᵥ v.tail)) :
        List.Vector ℕ (n + 1) → ℕ) : List.Vector ℕ (n + 1) →. ℕ) := by
  refine lamDef_of_inner (recMap φf φg) _ (fun v c hc => ?_)
    (fun v hv => by rw [PFun.coe_val] at hv; exact absurd trivial hv)
  rw [PFun.coe_val, Part.mem_some_iff] at hc
  subst hc
  obtain ⟨d, u, rfl⟩ := List.Vector.exists_eq_cons v
  rw [List.Vector.head_cons, List.Vector.tail_cons]
  exact recMap_eval φf φg f₀ g₀ hf hg u d

end Prec
end DomainTheory.NeighbourhoodSystems.Theorem56Full
