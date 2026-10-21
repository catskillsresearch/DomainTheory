/-ai
If every finite set of tokens is consistent, there is a unique total element.

The top element is total, and every total element equals the top element.
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


theorem exists_unique_total_of_allConsistent (h : sys.AllConsistent) :
    ∃! x : sys.Element, sys.IsTotal x :=
  ⟨sys.topElement h, ⟨sys.topElement_isTotal h, fun _ hy =>
    sys.eq_topElement_of_isTotal h hy⟩⟩

end InfoSys
end DomainTheory.InformationSystems
