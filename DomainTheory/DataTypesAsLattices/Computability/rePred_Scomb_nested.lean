/-ai
The predicate which holds when pack4_proj4 t lies in the application of the finite set coded by pack4_proj1 t to the finite set coded by pack4_proj3 t, itself applied to the application of the finite set coded by pack4_proj2 t to the finite set coded by pack4_proj3 t, is recursively enumerable.

Existentially quantify the primitive-recursive relation primrecRel_Scomb_app after swapping its arguments and passing from a computable predicate to a recursively enumerable one. The resulting predicate is identical to the stated one.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
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
