module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- `t` does not depend on environment slot `i`. -/
def Term.Avoids (i : ℕ) : Term → Prop
  | .var j => j ≠ i
  | .zero => True
  | .succ t => t.Avoids i
  | .pred t => t.Avoids i
  | .cond z x y => z.Avoids i ∧ x.Avoids i ∧ y.Avoids i
  | .app u x => u.Avoids i ∧ x.Avoids i
  | .lam j body => j = i ∨ body.Avoids i

end DomainTheory.DataTypesAsLattices
