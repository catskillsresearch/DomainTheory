
module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Computability.primrec_realized
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_secondRecSubst

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- A fixed combinator realizing `m ↦ apply(m)(num(m))`. -/
noncomputable def secondRecSubstC : Pomega :=
  (primrec_realized (Primrec.nat_iff.mp primrec_secondRecSubst)).choose

end DomainTheory.DataTypesAsLattices
