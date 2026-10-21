/-ai
A raw lambda token belonging to a finite set has depth at most the maximum depth of that set.

Unfold the maximum depth and induct on the underlying multiset. The empty multiset contributes no member. On a cons, the token is the head, whose depth is at most the maximum of the head depth and the fold of the tail, or it lies in the tail, whose inductive bound is at most that same maximum.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.maxDepthInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst31
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem le_finsetMaxDepth_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : t ∈ u) : rawDepth t ≤ finsetMaxDepth u := by
  simp only [finsetMaxDepth]
  have ht' : t ∈ u.1 := Finset.mem_def.1 ht
  revert ht'
  refine Multiset.induction_on u.1 ?_ ?_
  · intro ht'; cases ht'
  · intro a s ih ht'
    simp only [Multiset.mem_cons] at ht'
    simp only [Multiset.foldr_cons, maxDepthInsert]
    rcases ht' with rfl | ht'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht') (Nat.le_max_right _ _)

end InfoSys

end DomainTheory.InformationSystems
