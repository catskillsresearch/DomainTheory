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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_congr
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_comp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- **Composition of total functions** (the `Nat.Primrec'.comp` shape). -/
theorem lamDef_primComp {m nn : ℕ} (f₀ : List.Vector ℕ nn → ℕ)
    (g₀ : Fin nn → List.Vector ℕ m → ℕ)
    (φf : ApproximableMap 𝒩 N) (hf : LamDef φf (f₀ : List.Vector ℕ nn →. ℕ))
    (φg : Fin nn → ApproximableMap 𝒩 N) (hg : ∀ i, LamDef (φg i) (g₀ i : List.Vector ℕ m →. ℕ)) :
    LamDef (strictGuardN m (φf.comp (tupleMap nn φg)))
      ((fun a => f₀ (List.Vector.ofFn fun i => g₀ i a) : List.Vector ℕ m → ℕ) :
        List.Vector ℕ m →. ℕ) := by
  refine lamDef_congr (fun v => ?_)
    (lamDef_comp (f₀ : _ →. ℕ) (fun i => (g₀ i : _ →. ℕ)) φf hf φg hg)
  simp only [PFun.coe_val, Vector.mOfFn_part_some]
  change (Part.some (List.Vector.ofFn fun i => g₀ i v)).bind (fun w => Part.some (f₀ w))
      = Part.some (f₀ (List.Vector.ofFn fun i => g₀ i v))
  exact Part.bind_some _ _

end DomainTheory.NeighbourhoodSystems.Theorem56Full
