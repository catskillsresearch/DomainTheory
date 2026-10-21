/-ai
The S combinator is recursively enumerable.

Membership of the fourth component of a packed index in the indicated double application of finite sets is recursively enumerable, by composing the nested S-combinator predicate with projection to the second component. Conjoining the primitive recursive equation that unpacks a packed quadruple and existentially quantifying the index makes the predicate recursively enumerable. A witness unpacks, by the membership characterization of the S combinator, to four indices with the required application, and four such indices pack to a witness.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Computability.mem_Scomb_iff
public import DomainTheory.DataTypesAsLattices.Computability.rePred_Scomb_nested
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_Scomb_eq

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

theorem IsRE.Scomb : IsRE Scomb := by
  have hmem : REPred fun q : ℕ × ℕ =>
      pack4_proj4 q.2 ∈
        (e (pack4_proj1 q.2) ⬝ e (pack4_proj3 q.2)) ⬝
          (e (pack4_proj2 q.2) ⬝ e (pack4_proj3 q.2)) :=
    rePred_Scomb_nested.comp Primrec.snd.to_comp
  have hex : REPred fun p =>
      ∃ t, p = pair (pack4_proj1 t)
          (pair (pack4_proj2 t) (pair (pack4_proj3 t) (pack4_proj4 t))) ∧
        pack4_proj4 t ∈
          (e (pack4_proj1 t) ⬝ e (pack4_proj3 t)) ⬝
            (e (pack4_proj2 t) ⬝ e (pack4_proj3 t)) :=
    REPred.exists (REPred.and primrecPred_Scomb_eq.computablePred.to_re hmem)
  refine hex.of_eq fun p => ?_
  constructor
  · intro ⟨t, ht, hm⟩
    exact (mem_Scomb_iff p).mpr
      ⟨pack4_proj1 t, pack4_proj2 t, pack4_proj3 t, pack4_proj4 t, ht, hm⟩
  · intro hp
    obtain ⟨n0, n1, n2, m, ht, hm⟩ := (mem_Scomb_iff p).mp hp
    refine ⟨pack4 n0 n1 n2 m, ?_, ?_⟩
    · simpa [pack4, pack4_proj1, pack4_proj2, pack4_proj3, pack4_proj4,
        Nat.unpair_pair] using ht
    · simpa [pack4, pack4_proj1, pack4_proj2, pack4_proj3, pack4_proj4,
        Nat.unpair_pair] using hm

end DomainTheory.DataTypesAsLattices
