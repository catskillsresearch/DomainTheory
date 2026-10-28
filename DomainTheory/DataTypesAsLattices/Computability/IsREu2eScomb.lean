module
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eempty
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2etrue
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.mem_Scomb_iff
public import DomainTheory.DataTypesAsLattices.Computability.rePred_Scomb_nested
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_Scomb_eq

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Retracts.comp
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.Scomb : IsRE Scomb := by
  have hmem : REPred fun q : ℕ × ℕ =>
      pack4.proj4 q.2 ∈
        (e (pack4.proj1 q.2) ⬝ e (pack4.proj3 q.2)) ⬝
          (e (pack4.proj2 q.2) ⬝ e (pack4.proj3 q.2)) :=
    rePred_Scomb_nested.comp Primrec.snd.to_comp
  have hex : REPred fun p =>
      ∃ t, p = pair (pack4.proj1 t)
          (pair (pack4.proj2 t) (pair (pack4.proj3 t) (pack4.proj4 t))) ∧
        pack4.proj4 t ∈
          (e (pack4.proj1 t) ⬝ e (pack4.proj3 t)) ⬝
            (e (pack4.proj2 t) ⬝ e (pack4.proj3 t)) :=
    REPred.exists (REPred.and primrecPred_Scomb_eq.computablePred.to_re hmem)
  constructor
  refine hex.of_eq fun p => ?_
  constructor
  · intro ⟨t, ht, hm⟩
    exact (mem_Scomb_iff p).mpr
      ⟨pack4.proj1 t, pack4.proj2 t, pack4.proj3 t, pack4.proj4 t, ht, hm⟩
  · intro hp
    obtain ⟨n0, n1, n2, m, ht, hm⟩ := (mem_Scomb_iff p).mp hp
    refine ⟨pack4 n0 n1 n2 m, ?_, ?_⟩
    · simpa [pack4, pack4.proj1, pack4.proj2, pack4.proj3, pack4.proj4,
        Nat.unpair_pair] using ht
    · simpa [pack4, pack4.proj1, pack4.proj2, pack4.proj3, pack4.proj4,
        Nat.unpair_pair] using hm

end DomainTheory.DataTypesAsLattices
