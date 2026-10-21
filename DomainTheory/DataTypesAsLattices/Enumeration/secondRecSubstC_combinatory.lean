/-ai
The substitution combinator is combinatory.

It is the element chosen by the realization theorem for the primitive recursive substitution, and that choice is combinatory.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_secondRecSubst
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecSubstC

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem secondRecSubstC_combinatory : IsCombinatory secondRecSubstC :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose_spec.1

end DomainTheory.DataTypesAsLattices
