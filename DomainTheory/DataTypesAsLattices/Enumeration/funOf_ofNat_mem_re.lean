/-ai
If an element u is recursively enumerable, then the predicate of pairs whose second component lies in the application of u to the numeral of the first component is recursively enumerable.

Pair membership in u, composed with the primitive recursive map sending a pair to the pair of 0 with its second component, is recursively enumerable, and so is the same membership composed with the map sending a pair to the pair of 2 raised to the first component with the second component. The disjunction of these two predicates agrees, by the membership law for application to a numeral, with the stated predicate.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.mem_funOf_ofNat

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
