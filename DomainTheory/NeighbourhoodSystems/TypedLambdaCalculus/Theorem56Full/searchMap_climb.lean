module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.searchMap_step_found
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.searchMap_step_next

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





/-- **Capstone (least zero ⟹ value).** If `m` is a zero of `f(· ::ᵥ v)` and nothing below it is, then
starting from any counter `j ≤ m` the search returns `m`. (Downward induction on `m - j`.) -/
theorem searchMap_climb {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (m : ℕ)
    (hm0 : f (m ::ᵥ v) = 0) (hmin : ∀ i, i < m → f (i ::ᵥ v) ≠ 0) :
    ∀ d j, j + d = m → (searchMap φf).toElementMap (vecElem (j ::ᵥ v)) = natElem m := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hjm : j = m := by omega
    rw [hjm]
    exact searchMap_step_found φf hf v m hm0
  | succ d ih =>
    intro j hj
    have hjm : j < m := by omega
    rw [searchMap_step_next φf hf v j (hmin j hjm)]
    exact ih (j + 1) (by omega)

end Rfind
end DomainTheory.NeighbourhoodSystems.Theorem56Full
