module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairW
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_triangle
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_unpairW
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem primrec_unpairComp : Primrec unpairComp := by
  have h : Primrec fun k : ℕ =>
      (unpairW k - (k - triangle (unpairW k)), k - triangle (unpairW k)) :=
    Primrec.pair
      (Primrec.nat_sub.comp primrec_unpairW
        (Primrec.nat_sub.comp Primrec.id (primrec_triangle.comp primrec_unpairW)))
      (Primrec.nat_sub.comp Primrec.id (primrec_triangle.comp primrec_unpairW))
  exact h.of_eq fun k => by
    simp [unpairComp, unpairW.eq]

end DomainTheory.DataTypesAsLattices
