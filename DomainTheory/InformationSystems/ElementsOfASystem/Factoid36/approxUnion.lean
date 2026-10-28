
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def approxUnion (x : sys.Element) : Set α :=
  {a | ∃ (u : Finset α) (hu : u ∈ sys.Con),
    ↑u ⊆ x.carrier ∧ a ∈ (sys.closure u hu).carrier}

end InfoSys

end DomainTheory.InformationSystems
