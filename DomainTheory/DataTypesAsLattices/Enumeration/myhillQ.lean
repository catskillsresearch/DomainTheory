/-ai
Appendix q of Theorem 3.5. Relative to a valuation and a function p, the Myhill set consists of the pairs (j, m) such that m belongs to the value of p at the finite code of j.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.fin

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Appendix `q` of Theorem 3.5: `q = {(j,m) | m ∈ val(p(fin j))}`. -/
def myhillQ (val : ℕ → Pomega) (p : ℕ → ℕ) : Pomega :=
  {k | ∃ j m, k = pair j m ∧ m ∈ val (p (fin j))}

end DomainTheory.DataTypesAsLattices
