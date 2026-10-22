/-ai
The value of a λ-definition of a partial function, at the argument element of a total vector, is either bottom or the numeral for some natural number.

If the partial function is defined at that vector, the definedness clause returns the numeral for its value. If it is undefined there, the undefinedness clause returns bottom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- The value a realiser takes on a total argument is total-or-`⊥` (arg-like). -/
theorem realizer_value {n : ℕ} {φ : ApproximableMap 𝒩 N} {f : List.Vector ℕ n →. ℕ}
    (h : LamDef φ f) (v : List.Vector ℕ n) :
    φ.toElementMap (vecElem v) = N.bot ∨ ∃ k, φ.toElementMap (vecElem v) = natElem k := by
  by_cases hd : (f v).Dom
  · exact Or.inr ⟨(f v).get hd, h.defined v _ (Part.get_mem hd)⟩
  · exact Or.inl (h.undef v hd)

end DomainTheory.NeighbourhoodSystems.Theorem56Full
