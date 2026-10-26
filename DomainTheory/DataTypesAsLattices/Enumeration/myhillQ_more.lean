module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillQ
public import DomainTheory.DataTypesAsLattices.Enumeration.mem_myhillQ
public import DomainTheory.DataTypesAsLattices.Enumeration.funOf_ofNat_mem_re
public import DomainTheory.DataTypesAsLattices.Enumeration.realizes_valNat_mem
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_fin
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_unpairComp
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_codes
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

namespace myhillQ

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem isRE {u : Pomega} {p : ℕ → ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p) :
    IsRE (myhillQ valNat p) := by
  have hmem : REPred fun q : ℕ × ℕ =>
      q.2 ∈ valNat (p (fin q.1)) := by
    have hinner : REPred fun q : (ℕ × ℕ) × ℕ =>
        q.2 ∈ funOf u (ofNat (fin q.1.1)) ∧ q.1.2 ∈ valNat q.2 :=
      REPred.and
        ((funOf_ofNat_mem_re (combinatory_isRE hu)).comp
          (Primrec.pair (primrec_fin.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to_comp)
        (valNat.mem_re.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)).to_comp)
    exact _root_.REPred.of_eq (REPred.exists_param (α := ℕ × ℕ) hinner) fun q =>
      (realizes_valNat_mem hr (fin q.1) q.2).symm
  constructor
  exact _root_.REPred.of_eq
    (hmem.comp (primrec_unpairComp.to_comp))
    fun k => (mem_myhillQ p k).symm

end myhillQ

end DomainTheory.DataTypesAsLattices
