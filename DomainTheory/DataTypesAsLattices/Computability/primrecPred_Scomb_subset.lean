module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_Scomb_bit

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Retracts.comp
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecPred_Scomb_subset :
    PrimrecPred fun p : ℕ × ℕ =>
      ∀ i < p.1, p.1.testBit i = false ∨
        i ∈ e (pack4.proj2 p.2) ⬝ e (pack4.proj3 p.2) :=
  (primrecRel_Scomb_bit.forall_lt.comp Primrec.fst
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => by
      simp [Nat.unpair_pair]

end DomainTheory.DataTypesAsLattices
