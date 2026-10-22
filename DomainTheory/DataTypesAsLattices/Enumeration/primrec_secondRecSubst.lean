module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_num
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecSubst

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec_secondRecSubst : Primrec secondRecSubst :=
  primrec_applyNat.comp Primrec.id primrec_num

end DomainTheory.DataTypesAsLattices
