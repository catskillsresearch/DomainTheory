/-ai
A term avoids an environment slot i when a variable occurrence is some other index, the constant zero avoids every slot, successor and predecessor preserve avoidance, a conditional or an application avoids i when each immediate subterm does, and an abstraction avoids i when its bound variable is i or its body avoids i.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85

@[expose] public section

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
