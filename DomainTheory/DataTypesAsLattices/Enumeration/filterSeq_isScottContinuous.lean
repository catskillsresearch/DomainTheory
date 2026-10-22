/-ai
The map sending v to the graph of the function taking j to the filter realizer applied to the pairing combinator at v and then at j is Scott continuous.

Continuity of a graph of this shape reduces to continuity in v at each fixed j. Theorem 1.3 composes continuity of application of the filter realizer with continuity of application on the left at j, and a second use of theorem 1.3 composes that left application with continuity of application of the pairing combinator.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem filterSeq_isScottContinuous :
    IsScottContinuous fun v =>
      graph (fun j => funOf filterRealizer (funOf (funOf pairComb v) j)) :=
  graph_const_isScottContinuous
    (fun v j => funOf filterRealizer (funOf (funOf pairComb v) j))
    (fun j =>
      theorem_1_3 (f := fun w => funOf filterRealizer w)
        (g := fun v => funOf (funOf pairComb v) j)
        (funOf_isScottContinuous filterRealizer)
        (theorem_1_3 (f := fun w => funOf w j) (g := fun v => funOf pairComb v)
          (funOf_isScottContinuous_left j)
          (funOf_isScottContinuous pairComb)))

end DomainTheory.DataTypesAsLattices
