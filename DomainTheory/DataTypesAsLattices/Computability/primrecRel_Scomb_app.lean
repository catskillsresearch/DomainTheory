/-ai
The relation between k and t which holds when the finite set coded by k is contained in the application of the finite set coded by pack4_proj2 t to the finite set coded by pack4_proj3 t, and the Cantor pair of k with pack4_proj4 t lies in the application of the finite set coded by pack4_proj1 t to the finite set coded by pack4_proj3 t, is primitive recursive.

Membership of that Cantor pair is primitive recursive by composing primrecRel_mem_funOf_e with the pairing of the first and third pack4 projections and with the pairing of k and the fourth projection, transported by Nat.unpair_pair. Conjoining this membership predicate with primrecPred_Scomb_subset, and transporting both directions by eSubset_funOf_e_iff, gives the relation.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_mem_funOf_e
public import DomainTheory.DataTypesAsLattices.Computability.eSubset_funOf_e_iff
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj1
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj3
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj4
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_Scomb_subset

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

theorem primrecRel_Scomb_app :
    PrimrecRel fun k t : ℕ =>
      e k ⊆ e (pack4_proj2 t) ⬝ e (pack4_proj3 t) ∧
        pair k (pack4_proj4 t) ∈ e (pack4_proj1 t) ⬝ e (pack4_proj3 t) := by
  have hmem : PrimrecPred fun p : ℕ × ℕ =>
      pair p.1 (pack4_proj4 p.2) ∈
        e (pack4_proj1 p.2) ⬝ e (pack4_proj3 p.2) :=
    (primrecRel_mem_funOf_e.comp
      (Primrec₂.natPair.comp (primrec_pack4_proj1.comp Primrec.snd)
        (primrec_pack4_proj3.comp Primrec.snd))
      (primrec_pair.comp Primrec.fst (primrec_pack4_proj4.comp Primrec.snd))).of_eq
      fun p => by simp [Nat.unpair_pair]
  refine (primrecPred_Scomb_subset.and hmem).of_eq fun p => ?_
  constructor
  · intro ⟨hs, hm⟩
    exact ⟨(eSubset_funOf_e_iff _ _ _).mpr hs, hm⟩
  · intro ⟨hs, hm⟩
    exact ⟨(eSubset_funOf_e_iff _ _ _).mp hs, hm⟩

end DomainTheory.DataTypesAsLattices
