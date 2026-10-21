/-ai
This file gathers and re-exports totality, all-consistency, and the top element as the setting for Scott's Factoid 3.4. A top element need not exist. It exists precisely when every finite set of tokens is consistent, in which case its carrier is the whole token set, and it is then the unique total element, that is, the unique maximal element of the domain.
ai-/

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
