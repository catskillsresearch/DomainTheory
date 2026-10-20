module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- A neighbourhood system `𝒟'` over `β` is **complete** when every filter `y ∈ |𝒟'|` is *fixed
by a unique point* `b ∈ β`: a neighbourhood `S` lies in `y` iff `b ∈ S`. (Scott: "*a filter is
fixed by a point iff it is the filter of all neighbourhoods containing that point*".) -/
def IsComplete {β : Type*} (V' : NeighborhoodSystem β) : Prop :=
  ∀ y : V'.Element, ∃! b : β, ∀ S, V'.mem S → (y.mem S ↔ b ∈ S)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
