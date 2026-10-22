
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.enumerationUnion_left_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.enumerationUnion_right_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem unionOperator_app (x y : Pomega) :
    funOf (funOf (graph (fun x => graph (fun y => x ∪ y))) x) y = x ∪ y := by
  have hx : IsScottContinuous (fun x => graph (fun y => x ∪ y)) :=
    graph_const_isScottContinuous (fun x y => x ∪ y)
      (fun y => enumerationUnion_left_isScottContinuous y)
  have h1 : funOf (graph (fun x => graph (fun y => x ∪ y))) x =
      graph (fun y => x ∪ y) :=
    beta hx x
  rw [h1]
  exact beta (enumerationUnion_right_isScottContinuous x) y

end DomainTheory.DataTypesAsLattices
