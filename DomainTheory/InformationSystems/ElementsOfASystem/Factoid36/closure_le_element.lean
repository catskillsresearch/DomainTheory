
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.approxUnion

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem closure_le_element (x : sys.Element) {u : Finset α} (hu : u ∈ sys.Con)
    (hsub : ↑u ⊆ x.carrier) : sys.closure u hu ≤ x := by
  intro a ha
  exact x.closed u a hsub ha

end InfoSys
end DomainTheory.InformationSystems
