/-ai
Inclusion of finite sets coded by natural numbers, the relation e n ⊆ e b, is primitive recursive.

The bit relation which says that bit k of the first component of a packed pair is false or bit k of the second component is true is primitive recursive, as a disjunction of two boolean test-bit predicates rewritten by Bool.not_eq_true. Bounded universal quantification of that relation, composed with the first projection and Cantor pairing, is primitive recursive, and the symmetric form of eSubset_e_iff together with Nat.unpair_pair identifies it with inclusion.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Computability.eSubset_e_iff

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecRel_eSubset : PrimrecRel fun n b : ℕ => e n ⊆ e b := by
  have hR : PrimrecRel fun k q : ℕ =>
      q.unpair.1.testBit k = false ∨ q.unpair.2.testBit k = true :=
    ((primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst)).not.or
      (primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst))).of_eq
      fun _ => by simp [Bool.not_eq_true]
  refine (hR.forall_lt.comp Primrec.fst
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => ?_
  simpa [Nat.unpair_pair] using (eSubset_e_iff p.1 p.2).symm

end DomainTheory.DataTypesAsLattices
