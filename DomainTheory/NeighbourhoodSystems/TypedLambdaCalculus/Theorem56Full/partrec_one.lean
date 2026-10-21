/-ai
A partial recursive function of one natural number, presented as a partial recursive function of a length-one vector, is denoted by an approximable map from N to N that returns the numeral for each value, returns bottom where the function diverges, and sends bottom to bottom.

Apply λ-definability of partial recursive functions to the vector form, and compose the resulting map with the one-argument embedding. On a defined value, the embedding turns the numeral into the corresponding length-one argument, and the definedness clause, rewritten along the head of a cons, returns the numeral. On an undefined value the same rewriting uses the undefinedness clause. On bottom, the embedding sends bottom to the bottom argument, and the strictness clause at its zeroth coordinate returns bottom.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.partrec_lamDef
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.oneArg_natElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.oneArg_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)


/-- **Scott's 1-ary meta-theorem.** A partial recursive `h : ℕ →. ℕ` (presented as a unary
`Nat.Partrec'`) is denoted by a single approximable map `τ : N → N` that is correct on values,
divergent where `h` diverges, and strict. -/
theorem partrec_one {h : ℕ →. ℕ}
    (H : Nat.Partrec' (fun v : List.Vector ℕ 1 => h v.head)) :
    ∃ τ : ApproximableMap N N,
      (∀ a m, m ∈ h a → τ.toElementMap (natElem a) = natElem m) ∧
      (∀ a, ¬ (h a).Dom → τ.toElementMap (natElem a) = N.bot) ∧
      τ.toElementMap N.bot = N.bot := by
  obtain ⟨φ, hφ⟩ := partrec_lamDef H
  refine ⟨φ.comp oneArg, ?_, ?_, ?_⟩
  · intro a m hm
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.defined (a ::ᵥ List.Vector.nil) m ?_
    rwa [List.Vector.head_cons]
  · intro a hdom
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.undef (a ::ᵥ List.Vector.nil) ?_
    rwa [List.Vector.head_cons]
  · rw [toElementMap_comp, oneArg_bot]
    refine hφ.strict 𝒩.bot (fun j => Or.inl (component_bot j)) 0 (by omega) (component_bot 0)

end DomainTheory.NeighbourhoodSystems.Theorem56Full
