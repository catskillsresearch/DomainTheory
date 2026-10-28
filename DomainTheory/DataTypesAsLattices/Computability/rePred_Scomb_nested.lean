module

public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_Scomb_app

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem rePred_Scomb_nested :
    REPred fun t : ℕ =>
      pack4.proj4 t ∈
        (e (pack4.proj1 t) ⬝ e (pack4.proj3 t)) ⬝
          (e (pack4.proj2 t) ⬝ e (pack4.proj3 t)) :=
  (REPred.exists (p := fun t k =>
      e k ⊆ e (pack4.proj2 t) ⬝ e (pack4.proj3 t) ∧
        pair k (pack4.proj4 t) ∈ e (pack4.proj1 t) ⬝ e (pack4.proj3 t))
    (primrecRel_Scomb_app.swap.computablePred.to_re)).of_eq fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
