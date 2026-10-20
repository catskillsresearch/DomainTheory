module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code





































theorem seq2_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun b => seq2 a b) :=
  graph_const_isScottContinuous
    (fun b z => condSet z a (condSet (predSet z) b botElem))
    (fun z => theorem_1_3 (condSet_isScottContinuous_right z a)
      (condSet_isScottContinuous_mid (predSet z) botElem))

end DomainTheory.DataTypesAsLattices
