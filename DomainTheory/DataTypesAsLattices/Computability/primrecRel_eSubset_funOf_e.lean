/-ai
The relation which holds when the finite set coded by k is contained in the application of the two finite sets coded by the components of q is primitive recursive.

Apply the bounded universal quantifier forall_lt to primrecRel_eSubset_funOf_e_bit, composed with the first projection and Cantor pairing. After Nat.unpair_pair, the symmetric form of eSubset_funOf_e_iff identifies this quantified relation with the stated inclusion.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.eSubset_funOf_e_iff
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_eSubset_funOf_e_bit

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecRel_eSubset_funOf_e :
    PrimrecRel fun k q : ℕ =>
      e k ⊆ e (Nat.unpair q).1 ⬝ e (Nat.unpair q).2 := by
  refine (primrecRel_eSubset_funOf_e_bit.forall_lt.comp Primrec.fst
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => ?_
  simp only [Nat.unpair_pair]
  exact (eSubset_funOf_e_iff p.1 p.2.unpair.1 p.2.unpair.2).symm

end DomainTheory.DataTypesAsLattices
