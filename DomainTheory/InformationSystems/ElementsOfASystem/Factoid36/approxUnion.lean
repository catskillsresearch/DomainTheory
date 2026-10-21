/-ai
The approximation union of an element is the set of tokens that lie in the closure of some consistent finite set contained in the element.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- The set-theoretic union of all finite approximations of `x`. -/
def approxUnion (x : sys.Element) : Set α :=
  {a | ∃ (u : Finset α) (hu : u ∈ sys.Con),
    ↑u ⊆ x.carrier ∧ a ∈ (sys.closure u hu).carrier}

end InfoSys

end DomainTheory.InformationSystems
