module

public import Mathlib.Computability.Halting
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
