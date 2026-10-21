/-ai
A continuous unary map on the lattice of sets of natural numbers is computable when its graph is recursively enumerable.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.IsRE

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §2, Definition.** A continuous `k`-ary map is computable
when membership in its values on finite arguments is r.e. Unary case: -/
def IsComputable (f : Pomega → Pomega) : Prop :=
  IsScottContinuous f ∧ IsRE (graph f)

end DomainTheory.DataTypesAsLattices
