module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec_num : Primrec num :=
  (Primrec.nat_rec' (f := id) (g := fun _ => (1 : ℕ))
    (h := fun (_ : ℕ) (p : ℕ × ℕ) => applyNat 12 p.2)
    Primrec.id (Primrec.const 1)
    (show Primrec fun q : ℕ × ℕ × ℕ => applyNat 12 q.2.2 from
      primrec_applyNat.comp (Primrec.const 12) (Primrec.snd.comp Primrec.snd))).of_eq
    fun n => by
      induction n with
      | zero => rfl
      | succ n ih =>
        change applyNat 12 (Nat.rec 1 (fun n IH => applyNat 12 (n, IH).2) n) =
          applyNat 12 (num n)
        have ih' : Nat.rec 1 (fun n IH => applyNat 12 (n, IH).2) n = num n := by
          simpa [id] using ih
        rw [ih']

end DomainTheory.DataTypesAsLattices
