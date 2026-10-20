/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)





















/-- If `u` has function tokens at stage `n`, some earlier right branch supplies FunCon. -/
theorem LamConN_exists_FunCon {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hne : lamFunFinset u ≠ ∅) :
    ∃ k, k + 1 ≤ n ∧ lamAtomFinset u = ∅ ∧
      (∀ p ∈ lamFunFinset u,
        LamConN A k (listToFinset p.1) ∧ LamConN A k (listToFinset p.2)) ∧
      (∀ s ⊆ lamFunFinset u,
        LamConN A k (lamInputUnion s) → LamConN A k (lamOutputUnion s)) := by
  induction n generalizing u with
  | zero => exact False.elim (hne hu.2)
  | succ n ih =>
    rcases hu with hu | ⟨hA, hWF, hFun⟩
    · rcases ih hu hne with ⟨k, hk, H⟩
      exact ⟨k, Nat.le_succ_of_le hk, H⟩
    · exact ⟨n, Nat.le_refl _, hA, hWF, hFun⟩

end InfoSys
end DomainTheory.InformationSystems
