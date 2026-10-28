
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.IsTotal
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.AllConsistent
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34.topElement

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem exists_top_iff_allConsistent :
    (∃ x : sys.Element, x.carrier = Set.univ) ↔ sys.AllConsistent := by
  constructor
  · intro ⟨x, hx⟩ u
    exact x.consistent u (hx ▸ Set.subset_univ _)
  · intro h
    exact ⟨sys.topElement h, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
