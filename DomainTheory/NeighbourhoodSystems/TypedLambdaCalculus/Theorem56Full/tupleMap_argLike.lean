module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_tupleMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.realizer_value
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_tupleMap_ge

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- The tuple of realisers, applied to a total argument, is arg-like. -/
theorem tupleMap_argLike {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i)) (v : List.Vector ℕ m) :
    ArgLike ((tupleMap nn φg).toElementMap (vecElem v)) := by
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi]; exact realizer_value (hg ⟨i, hi⟩) v
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi)]; exact Or.inl rfl

end DomainTheory.NeighbourhoodSystems.Theorem56Full
