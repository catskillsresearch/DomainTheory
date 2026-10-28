module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

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

namespace valNat

theorem zero : valNat 0 = Gcomb := by
  unfold valNat
  rw [Nat.strongRec]

theorem succ (n : ℕ) :
    valNat (n + 1) = valNat (unpair n).1 ⬝ valNat (unpair n).2 := by
  unfold valNat
  rw [Nat.strongRec]

theorem app (n m : ℕ) :
    valNat (applyNat n m) = valNat n ⬝ valNat m := by
  rw [applyNat, succ, unpair_pair]

theorem combinatory : ∀ n, IsCombinatory (valNat n)
  | 0 => zero ▸ Gcomb.combinatory
  | n + 1 =>
    succ n ▸
      .app (combinatory (unpair n).1) (combinatory (unpair n).2)
decreasing_by
  · exact (pair_lt_left (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)
  · exact (pair_lt_right (unpair n).1 (unpair n).2).trans_le (by
      have := pair_unpair n
      omega)

end valNat

end DomainTheory.DataTypesAsLattices
