/-ai
Top lies in the range of a ⊕ b.

The range equation is the reverse of the law that the sum sends top to top.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app_top

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem plusR_typed_top (a b : Pomega) : typed topElem (plusR a b) :=
  (plusR_app_top a b).symm

end DomainTheory.DataTypesAsLattices
