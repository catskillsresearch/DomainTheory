module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Computability.primrecRel_Scomb_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

theorem rePred_Scomb_nested :
    REPred fun t : ℕ =>
      pack4_proj4 t ∈
        (e (pack4_proj1 t) ⬝ e (pack4_proj3 t)) ⬝
          (e (pack4_proj2 t) ⬝ e (pack4_proj3 t)) :=
  (REPred.exists (p := fun t k =>
      e k ⊆ e (pack4_proj2 t) ⬝ e (pack4_proj3 t) ∧
        pair k (pack4_proj4 t) ∈ e (pack4_proj1 t) ⬝ e (pack4_proj3 t))
    (primrecRel_Scomb_app.swap.computablePred.to_re)).of_eq fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
