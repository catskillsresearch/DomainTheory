module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_tupleMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.lamDef_of_inner
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.tupleMap_vecElem_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.tupleMap_argLike
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.mem_mOfFn

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)



















/-- **Composition** (Scott's multivariate composition). If `f` and each `gᵢ` are λ-defined, so is
`v ↦ (⟨g₀ v, …, g_{nn-1} v⟩) >>= f`. -/
theorem lamDef_comp {m nn : ℕ} (f : List.Vector ℕ nn →. ℕ) (g : Fin nn → List.Vector ℕ m →. ℕ)
    (φf : ApproximableMap 𝒩 N) (hf : LamDef φf f)
    (φg : Fin nn → ApproximableMap 𝒩 N) (hg : ∀ i, LamDef (φg i) (g i)) :
    LamDef (strictGuardN m (φf.comp (tupleMap nn φg)))
      (fun v => (List.Vector.mOfFn fun i => g i v) >>= f) := by
  refine lamDef_of_inner (φf.comp (tupleMap nn φg)) _ ?_ ?_
  · intro v c hc
    have hc' : c ∈ (List.Vector.mOfFn fun i => g i v).bind (fun w => f w) := hc
    rw [Part.mem_bind_iff] at hc'
    obtain ⟨w, hw, hcw⟩ := hc'
    rw [toElementMap_comp, tupleMap_vecElem_eq φg g hg v w ((mem_mOfFn _ w).mp hw)]
    exact hf.defined w c hcw
  · intro v hv
    rw [toElementMap_comp]
    by_cases hall : ∀ i, (g i v).Dom
    · set w : List.Vector ℕ nn := List.Vector.ofFn (fun i => (g i v).get (hall i)) with hw_def
      have hwget : ∀ i, w.get i ∈ g i v := by
        intro i; rw [hw_def, List.Vector.get_ofFn]; exact Part.get_mem (hall i)
      rw [tupleMap_vecElem_eq φg g hg v w hwget]
      refine hf.undef w (fun hfw => hv ?_)
      have hmem : (f w).get hfw ∈ (List.Vector.mOfFn fun i => g i v).bind (fun w => f w) := by
        rw [Part.mem_bind_iff]
        exact ⟨w, (mem_mOfFn _ w).mpr hwget, Part.get_mem hfw⟩
      exact Part.dom_iff_mem.mpr ⟨_, hmem⟩
    · rw [not_forall] at hall
      obtain ⟨j, hj⟩ := hall
      refine hf.strict ((tupleMap nn φg).toElementMap (vecElem v))
        (tupleMap_argLike φg g hg v) j j.isLt ?_
      rw [component_tupleMap nn φg (vecElem v) j j.isLt, Fin.eta]
      exact (hg j).undef v hj

end DomainTheory.NeighbourhoodSystems.Theorem56Full
