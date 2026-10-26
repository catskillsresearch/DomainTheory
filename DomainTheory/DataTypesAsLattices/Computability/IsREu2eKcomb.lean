module
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eempty
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2etrue
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Computability.mem_graph_const_iff
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2egraph_of_re

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.Kcomb : IsRE Kcomb :=
  IsRE.graph_of_re (f := fun x => graph (fun _ => x)) <| by
    have hP : PrimrecPred fun w : ℕ × ℕ =>
        (Nat.unpair w.1).2 = pair (Nat.unpair w.2).1 (Nat.unpair w.2).2 ∧
          (Nat.unpair w.1).1.testBit (Nat.unpair w.2).2 = true :=
      (Primrec.eq.comp
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
          (primrec_pair.comp
            (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))).and
        (primrecPred_bool (Primrec₂.comp primrec_testBit
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
    have hex : REPred fun w : ℕ =>
        ∃ t, (Nat.unpair w).2 = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
          (Nat.unpair w).1.testBit (Nat.unpair t).2 = true :=
      REPred.exists hP.computablePred.to_re
    exact _root_.REPred.of_eq
      (hex.comp (Primrec₂.natPair.comp Primrec.fst Primrec.snd).to_comp)
      fun q => by
        simp only [Nat.unpair_pair]
        exact (mem_graph_const_iff q.1 q.2).symm

end DomainTheory.DataTypesAsLattices
