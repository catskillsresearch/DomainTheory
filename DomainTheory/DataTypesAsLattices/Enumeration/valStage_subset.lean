/-ai
For every stage s and every code n, the application of the s-fold iterate of the enumerator step from bottom to the numeral of n is contained in the numerical value of n.

The proof recurses on the stage. At stage zero the iterate is bottom, and the application of bottom is empty. At a successor stage and argument zero, both sides equal the G combinator. At a successor stage and a successor argument, the successor clauses reduce the inclusion to monotonicity of application in each argument, applied to the two inductive inclusions for the unpairing components.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep_app_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep_app_succ

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



































theorem valStage_subset : ∀ s n,
    funOf (iterateBot valStep s) (ofNat n) ⊆ valNat n
  | 0, n => by simp [iterateBot, funOf, botElem]
  | s + 1, 0 => by
      rw [iterateBot, valStep_app_zero, valNat_zero]
  | s + 1, p + 1 => by
      rw [iterateBot, valStep_app_succ, valNat_succ]
      exact subset_trans
        (funOf_monotone_left
          (valStage_subset s (unpair p).1)
          (funOf (iterateBot valStep s) (ofNat (unpair p).2)))
        (funOf_monotone_right (valNat (unpair p).1)
          (valStage_subset s (unpair p).2))

end DomainTheory.DataTypesAsLattices
