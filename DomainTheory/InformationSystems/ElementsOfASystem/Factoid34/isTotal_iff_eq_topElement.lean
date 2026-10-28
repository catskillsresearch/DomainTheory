
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.IsTotal
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.AllConsistent
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.topElement
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
