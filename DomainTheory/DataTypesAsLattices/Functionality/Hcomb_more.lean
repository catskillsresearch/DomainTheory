module

public import DomainTheory.DataTypesAsLattices.Functionality.Hcomb
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_45
public import DomainTheory.DataTypesAsLattices.Functionality.Htyped
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace Hcomb

theorem decode (τ : LambTerm) :
    funOf Hcomb (encodeExp τ) = Htyped τ :=
  (DomainTheory.DataTypesAsLattices.eq_4_45 τ).2.2

end Hcomb

end DomainTheory.DataTypesAsLattices
