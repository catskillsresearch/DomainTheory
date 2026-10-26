module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.primrec_twoPow
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.mem_funOf_ofNat
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2epair_mem

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem funOf_ofNat_mem_re {u : Pomega} (hu : IsRE u) :
    REPred fun q : ℕ × ℕ => q.2 ∈ funOf u (ofNat q.1) := by
  have h0 : REPred fun q : ℕ × ℕ => pair 0 q.2 ∈ u :=
    (IsRE.pair_mem hu).comp
      (Primrec.pair (Primrec.const 0) Primrec.snd).to_comp
  have hpow : REPred fun q : ℕ × ℕ => pair (2 ^ q.1) q.2 ∈ u :=
    (IsRE.pair_mem hu).comp
      (Primrec.pair (primrec_twoPow.comp Primrec.fst) Primrec.snd).to_comp
  exact _root_.REPred.of_eq (REPred.or h0 hpow) fun q =>
    (mem_funOf_ofNat u q.1 q.2).symm

end DomainTheory.DataTypesAsLattices
