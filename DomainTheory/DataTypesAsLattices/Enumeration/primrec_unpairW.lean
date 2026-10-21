/-ai
The witness used by computational unpairing is primitive recursive.

It agrees with the primitive recursion that starts at 0 and, given the argument k and the previous pair, keeps the previous second component when k is strictly below the triangular number of one more than the previous first component, and otherwise returns one more than that first component. The comparison is primitive recursive because the triangular-number function is primitive recursive.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_triangle

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem primrec_unpairW : Primrec unpairW :=
  (Primrec.nat_rec' (f := id) (g := fun _ => (0 : ℕ))
    (h := fun k (p : ℕ × ℕ) => if k < triangle (p.1 + 1) then p.2 else p.1 + 1)
    Primrec.id (Primrec.const 0)
    (Primrec.ite (c := fun q : ℕ × ℕ × ℕ => q.1 < triangle (q.2.1 + 1))
      (Primrec.nat_lt.comp Primrec.fst
        (primrec_triangle.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))).of_eq fun _ => rfl

end DomainTheory.DataTypesAsLattices
