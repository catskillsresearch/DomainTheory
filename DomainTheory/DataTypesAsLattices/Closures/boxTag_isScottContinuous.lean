/-ai
The occupancy tag at a fixed index is Scott continuous.

The tag is the conditional set with both branches equal to the singleton of that index, and a conditional set is Scott continuous in the tested set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxTag_isScottContinuous (i : ℕ) : IsScottContinuous (boxTag i) := by
  have hfun : boxTag i = fun z => condSet z (ofNat i) (ofNat i) := rfl
  rw [hfun]
  exact condSet_isScottContinuous_left (ofNat i) (ofNat i)

end DomainTheory.DataTypesAsLattices
