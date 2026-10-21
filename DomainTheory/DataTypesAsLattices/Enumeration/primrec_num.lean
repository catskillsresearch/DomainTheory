/-ai
The numeral code is primitive recursive.

It is the primitive recursion with value 1 at zero and with successor step the application of code 12 to the previous value. Agreement with the numeral code is by induction on the argument: the zero case is the constant 1, and the successor case rewrites the recursive clause by the inductive hypothesis.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat

@[expose] public section

set_option linter.unusedSectionVars false

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
