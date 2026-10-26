
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Enumeration.enumBottomTerm
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Enumeration.interp_avoids
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.seq2

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Term-level binary sequence constructor. -/
def seq2Term (a b : Term) : Term :=
  .lam 8 (.cond (.var 8) a
    (.cond (.pred (.var 8)) b enumBottomTerm))

namespace seq2Term

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem avoids8 (a b : Term) : (seq2Term a b).Avoids 8 :=
  Or.inl rfl

theorem interp (a b : Term) (ρ : ℕ → Pomega)
    (ha : a.Avoids 8) (hb : b.Avoids 8) :
    interp (seq2Term a b) ρ = seq2 (interp a ρ) (interp b ρ) := by
  unfold seq2Term seq2
  apply congrArg graph
  funext z
  simp only [_root_.DomainTheory.DataTypesAsLattices.interp]
  rw [interp_avoids a ρ z ha, interp_avoids b ρ z hb, enumBottomTerm.interp]
  simp [envSet, Function.update]

end seq2Term

end DomainTheory.DataTypesAsLattices
