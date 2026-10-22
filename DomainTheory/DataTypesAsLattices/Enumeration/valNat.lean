module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.7) / Theorem 3.2.** `val(0) = G` and
`val(apply(n)(m)) = val(n)(val(m))`. -/
noncomputable def valNat : ℕ → Pomega :=
  Nat.strongRec fun n rec =>
    match n with
    | 0 => Gcomb
    | n + 1 =>
        rec (unpair n).1
          (Nat.lt_of_lt_of_eq
            (pair_lt_left (unpair n).1 (unpair n).2)
            (congrArg (fun x => x + 1) (pair_unpair n))) ⬝
        rec (unpair n).2
          (Nat.lt_of_lt_of_eq
            (pair_lt_right (unpair n).1 (unpair n).2)
            (congrArg (fun x => x + 1) (pair_unpair n)))

end DomainTheory.DataTypesAsLattices
