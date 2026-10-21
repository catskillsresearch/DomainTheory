/-ai
The map sending a set u to the conditional set that tests u and returns the singleton zero or the successor of the full set is Scott continuous.

This is the left continuity of conditional sets, applied to those two constant branches.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boool_map_isScottContinuous :
    IsScottContinuous (fun u => condSet u (ofNat 0) (succSet topElem)) :=
  condSet_isScottContinuous_left (ofNat 0) (succSet topElem)

end DomainTheory.DataTypesAsLattices
