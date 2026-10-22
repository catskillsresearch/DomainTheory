/-ai
Computational unpairing is primitive recursive.

The pair whose first component is the unpairing witness minus the excess of the argument over the triangular number of that witness, and whose second component is that excess, is primitive recursive, because the witness, subtraction, and triangular numbers are primitive recursive. The pair agrees with computational unpairing by the equation for the witness.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_triangle
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_unpairW
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairW_eq

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
    simp [unpairComp, unpairW_eq]

end DomainTheory.DataTypesAsLattices
