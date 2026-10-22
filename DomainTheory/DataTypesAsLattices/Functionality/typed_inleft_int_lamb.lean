
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inl
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC_app
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_39

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_inleft_int_lamb {x : Pomega} (hx : typed x intR) :
    typed (funOf inleftC x) lambR := by
  rw [eq_4_39, inleftC_app]
  exact plusR_typed_inl hx

end DomainTheory.DataTypesAsLattices
