module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term
public import DomainTheory.DataTypesAsLattices.Enumeration.seqConsTerm
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.enumBottomTerm
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more
public import DomainTheory.DataTypesAsLattices.Lambda.seqCons
public import DomainTheory.DataTypesAsLattices.Lambda.seq2
public import DomainTheory.DataTypesAsLattices.Graph.funOf

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def barPosTerm : Term :=
  seqConsTerm (.succ .zero)
    (seq2Term (.var 1) (.app (.var 2) (.succ .zero)))

namespace barPosTerm

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem interp (ρ : ℕ → Pomega) :
    _root_.DomainTheory.DataTypesAsLattices.interp barPosTerm ρ = barPos (ρ 1) (ρ 2) := by
  have hzero : Term.Avoids 7 (.succ .zero) := by simp [Term.Avoids]
  have hseq : Term.Avoids 7
      (seq2Term (.var 1) (.app (.var 2) (.succ .zero))) := by
    change _ ∨ _
    refine Or.inr ?_
    refine ⟨?_, ?_, ?_⟩
    · exact (by omega : (8 : ℕ) ≠ 7)
    · exact (by omega : (1 : ℕ) ≠ 7)
    · refine ⟨?_, ?_, enumBottomTerm.avoids 7⟩
      · exact (by omega : (8 : ℕ) ≠ 7)
      · exact ⟨(by omega : (2 : ℕ) ≠ 7), trivial⟩
  have h1 : Term.Avoids 8 (.var 1) := (by omega : (1 : ℕ) ≠ 8)
  have h2 : Term.Avoids 8 (.app (.var 2) (.succ .zero)) :=
    ⟨(by omega : (2 : ℕ) ≠ 8), trivial⟩
  rw [barPosTerm, seqConsTerm.interp _ _ _ hzero hseq,
    seq2Term.interp _ _ _ h1 h2]
  simp only [_root_.DomainTheory.DataTypesAsLattices.interp, barPos]
  simp [succSet.ofNat]

end barPosTerm

end DomainTheory.DataTypesAsLattices
