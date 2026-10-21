/-ai
When every finite set of tokens is consistent, an element is total if and only if it equals the top element.

Totality yields equality with the top element. Equality with the top element yields totality because the top element is total.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.topElement_isTotal
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.eq_topElement_of_isTotal

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




theorem isTotal_iff_eq_topElement (h : sys.AllConsistent) {x : sys.Element} :
    sys.IsTotal x ↔ x = sys.topElement h :=
  ⟨sys.eq_topElement_of_isTotal h, fun hx => hx ▸ sys.topElement_isTotal h⟩

end InfoSys
end DomainTheory.InformationSystems
