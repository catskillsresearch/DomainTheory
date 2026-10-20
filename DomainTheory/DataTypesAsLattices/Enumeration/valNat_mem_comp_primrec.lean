module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.REPredu2eexists_param
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_mem_re
public import DomainTheory.DataTypesAsLattices.Enumeration.realizes_valNat_mem
public import DomainTheory.DataTypesAsLattices.Enumeration.funOf_ofNat_mem_re

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code













theorem valNat_mem_comp_primrec {u : Pomega} {p s : ℕ → ℕ} {k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p) (hs : Primrec s) :
    REPred fun m => k ∈ valNat (p (s m)) := by
  have hinner : REPred fun q : ℕ × ℕ =>
      q.2 ∈ funOf u (ofNat (s q.1)) ∧ k ∈ valNat q.2 :=
    REPred.and
      ((funOf_ofNat_mem_re (combinatory_isRE hu)).comp
        (Primrec.pair (hs.comp Primrec.fst) Primrec.snd).to_comp)
      (valNat_mem_re.comp (Primrec.pair Primrec.snd (Primrec.const k)).to_comp)
  exact _root_.REPred.of_eq (REPred.exists_param (α := ℕ) hinner) fun m =>
    (realizes_valNat_mem hr (s m) k).symm

end DomainTheory.DataTypesAsLattices
