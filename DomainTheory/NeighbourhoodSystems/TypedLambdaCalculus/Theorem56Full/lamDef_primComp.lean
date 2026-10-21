/-ai
Composition of total functions, in the shape of the primitive-recursive composition constructor, preserves λ-definability. The realiser is the outer realiser composed with the tuple of the inner realisers, wrapped in the strict guard.

Transport the partial-composition theorem along a pointwise equality. For each vector, the monadic vector of the coerced total functions is the defined vector of their values, and binding the outer function through that defined value returns the outer function at the vector of values.
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
