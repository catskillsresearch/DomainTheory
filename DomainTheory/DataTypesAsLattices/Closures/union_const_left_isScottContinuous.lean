module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem union_const_left_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun x => c ∪ x) := by
  have : (fun x : Pomega => c ∪ x) = (fun x => x ∪ c) := by
    funext x; exact Set.union_comm c x
  rw [this]
  exact union_left_isScottContinuous c

end DomainTheory.DataTypesAsLattices
