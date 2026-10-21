/-ai
For a fixed element b, the map sending a to the binary sequence constructor of a and b is Scott continuous.

It is the graph of the family sending a and z to the conditional of z between a and the conditional of the predecessor of z between b and bottom, and for each z that conditional is Scott continuous in its middle argument.
ai-/

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






































theorem seq2_left_isScottContinuous (b : Pomega) :
    IsScottContinuous (fun a => seq2 a b) :=
  graph_const_isScottContinuous
    (fun a z => condSet z a (condSet (predSet z) b botElem))
    (fun z => condSet_isScottContinuous_mid z _)

end DomainTheory.DataTypesAsLattices
