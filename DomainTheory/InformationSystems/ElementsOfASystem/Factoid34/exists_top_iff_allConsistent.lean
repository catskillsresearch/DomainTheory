/-ai
An element whose carrier is the whole token set exists if and only if every finite set of tokens is consistent.

Such an element makes every finite set consistent, because every finite set is contained in its carrier. If every finite set is consistent, the top element is an element with full carrier.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- **Factoid 3.4.** Top `⊤ = D` exists as an element iff every finite subset is consistent. -/
theorem exists_top_iff_allConsistent :
    (∃ x : sys.Element, x.carrier = Set.univ) ↔ sys.AllConsistent := by
  constructor
  · intro ⟨x, hx⟩ u
    exact x.consistent u (hx ▸ Set.subset_univ _)
  · intro h
    exact ⟨sys.topElement h, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
