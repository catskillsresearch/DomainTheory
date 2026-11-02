module

public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd
public import Mathlib.Order.SetNotation
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def IsScottOpen (U : Set Pomega) : Prop :=
  ∃ B : Set ℕ, U = ⋃ n ∈ B, basicNhhd n

end DomainTheory.DataTypesAsLattices
