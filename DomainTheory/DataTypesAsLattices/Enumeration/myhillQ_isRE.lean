/-ai
If a combinatory element realizes a function p, then the Myhill set of the natural valuation and p is recursively enumerable.

The predicate of pairs (j, m) for which m lies in the natural value of p at the finite code of j is recursively enumerable. In an extra parameter c, the conjunction of membership of c in the application of the realizer to the numeral of the finite code of j and of membership of m in the natural value of c is recursively enumerable: the first factor uses recursive enumerability of application to a numeral for a combinatory element, composed with the primitive recursive finite-code map, and the second uses recursive enumerability of membership in natural values. Existential quantification over c agrees with the realization identity. Composing with computational unpairing and rewriting by the membership law for the Myhill set gives recursive enumerability of the set.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_fin
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_unpairComp
public import DomainTheory.DataTypesAsLattices.Enumeration.REPredu2eexists_param
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_mem_re
public import DomainTheory.DataTypesAsLattices.Enumeration.mem_myhillQ
public import DomainTheory.DataTypesAsLattices.Enumeration.realizes_valNat_mem
public import DomainTheory.DataTypesAsLattices.Enumeration.funOf_ofNat_mem_re

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem myhillQ_isRE {u : Pomega} {p : ℕ → ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p) :
    IsRE (myhillQ valNat p) := by
  have hmem : REPred fun q : ℕ × ℕ =>
      q.2 ∈ valNat (p (fin q.1)) := by
    have hinner : REPred fun q : (ℕ × ℕ) × ℕ =>
        q.2 ∈ funOf u (ofNat (fin q.1.1)) ∧ q.1.2 ∈ valNat q.2 :=
      REPred.and
        ((funOf_ofNat_mem_re (combinatory_isRE hu)).comp
          (Primrec.pair (primrec_fin.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to_comp)
        (valNat_mem_re.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)).to_comp)
    exact _root_.REPred.of_eq (REPred.exists_param (α := ℕ × ℕ) hinner) fun q =>
      (realizes_valNat_mem hr (fin q.1) q.2).symm
  exact _root_.REPred.of_eq
    (hmem.comp (primrec_unpairComp.to_comp))
    fun k => (mem_myhillQ p k).symm

end DomainTheory.DataTypesAsLattices
