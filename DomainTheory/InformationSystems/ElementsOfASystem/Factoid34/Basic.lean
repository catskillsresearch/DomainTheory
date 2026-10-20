module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.IsTotal
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.AllConsistent
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.topElement

@[expose] public section

/-!
# Factoid 3.4 — top element and total elements

**Factoid 3.4 (inventory / Scott §3).** There need be no top element `⊤`. Such an
element exists if and only if every finite subset of the token set is consistent, in
which case `⊤ = D` as a set. When it exists, it is the unique *total* (maximal)
element of the domain.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)



end InfoSys
end DomainTheory.InformationSystems
