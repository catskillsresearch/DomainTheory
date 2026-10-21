/-ai
If each entry of a vector w lies in the value of the corresponding partial function at a total vector v, and each map in the family is a λ-definition of that partial function, then the tuple of those maps, evaluated at the argument element of v, equals the argument element of w.

The two elements agree on every component. Below the tuple length, the component of the tuple is the defined value of the corresponding λ-definition, hence the numeral for the corresponding entry of w. At or beyond the tuple length both components are bottom.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.eq_of_component_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_tupleMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_vecElem_lt
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_tupleMap_ge

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)



















/-- The tuple of realisers, applied to a total argument, equals `vecElem w` where `wᵢ = gᵢ(v)`. -/
theorem tupleMap_vecElem_eq {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i))
    (v : List.Vector ℕ m) (w : List.Vector ℕ nn) (hw : ∀ i, w.get i ∈ g i v) :
    (tupleMap nn φg).toElementMap (vecElem v) = vecElem w := by
  apply eq_of_component_eq
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi, component_vecElem_lt w hi]
    exact (hg ⟨i, hi⟩).defined v (w.get ⟨i, hi⟩) (hw ⟨i, hi⟩)
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi), component_vecElem,
      dite_eq_right hi]

end DomainTheory.NeighbourhoodSystems.Theorem56Full
