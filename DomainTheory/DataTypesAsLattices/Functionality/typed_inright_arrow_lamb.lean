module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inr
public import DomainTheory.DataTypesAsLattices.Functionality.inrightC_app
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_39

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem typed_inright_arrow_lamb {x : Pomega}
    (hx : typed x (arrowR lambR lambR)) :
    typed (funOf inrightC x) lambR := by
  rw [eq_4_39, inrightC_app]
  exact plusR_typed_inr hx

end DomainTheory.DataTypesAsLattices
