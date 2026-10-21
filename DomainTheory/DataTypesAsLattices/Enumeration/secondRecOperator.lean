/-ai
The second recursion operator is the uniform operator sending an element u to the map m ↦ u(apply(m)(num(m))). It is introduced as S applied to K of the application combinator, applied to S(S(K S) K) of K of the substitution combinator.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecSubstC

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- The uniform operator `u ↦ λm∈ω. u(apply(m)(num(m)))`. -/
def secondRecOperator : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb
      (funOf (funOf Scomb (funOf Kcomb Scomb)) Kcomb))
      (funOf Kcomb secondRecSubstC))

end DomainTheory.DataTypesAsLattices
