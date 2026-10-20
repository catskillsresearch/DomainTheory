/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.enumBottomTerm_avoids
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.seqConsTerm_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











































theorem barPosTerm_interp (ρ : ℕ → Pomega) :
    interp barPosTerm ρ = barPos (ρ 1) (ρ 2) := by
  have hzero : Term.Avoids 7 (.succ .zero) := by simp [Term.Avoids]
  have hseq : Term.Avoids 7
      (seq2Term (.var 1) (.app (.var 2) (.succ .zero))) := by
    change _ ∨ _
    refine Or.inr ?_
    refine ⟨?_, ?_, ?_⟩
    · exact (by omega : (8 : ℕ) ≠ 7)
    · exact (by omega : (1 : ℕ) ≠ 7)
    · refine ⟨?_, ?_, enumBottomTerm_avoids 7⟩
      · exact (by omega : (8 : ℕ) ≠ 7)
      · exact ⟨(by omega : (2 : ℕ) ≠ 7), trivial⟩
  have h1 : Term.Avoids 8 (.var 1) := (by omega : (1 : ℕ) ≠ 8)
  have h2 : Term.Avoids 8 (.app (.var 2) (.succ .zero)) :=
    ⟨(by omega : (2 : ℕ) ≠ 8), trivial⟩
  rw [barPosTerm, seqConsTerm_interp _ _ _ hzero hseq,
    seq2Term_interp _ _ _ h1 h2]
  simp [interp, barPos, succSet_ofNat]

end DomainTheory.DataTypesAsLattices
