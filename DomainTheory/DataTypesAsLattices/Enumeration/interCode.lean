/-ai
The intersection code is a natural number chosen, by the surjectivity in theorem 3.2 applied to the combinatory intersection combinator, as a Gödel number of that combinator.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_2_surjective
public import DomainTheory.DataTypesAsLattices.Enumeration.interC_combinatory

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

noncomputable def interCode : ℕ :=
  (theorem_3_2_surjective interC_combinatory).choose

end DomainTheory.DataTypesAsLattices
