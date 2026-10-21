/-ai
A set of neighbourhoods belongs to the Smyth power domain when it is the union of the down-sets of the neighbourhoods appearing in some finite list. The empty list gives the empty union.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 7.9 — the Smyth power domain `ℙ𝒟`.** A set `W : Set (Set α)` is a
neighbourhood of `ℙ𝒟` iff it is a *finite union of down-sets* `⋃_{X ∈ L} ↓X` for some finite
list `L` of `𝒟`-neighbourhoods. The empty list `L = []` realizes Scott's `n = 0` (the empty
union `∅`). -/
def PDmem (W : Set (Set α)) : Prop :=
  ∃ L : List (Set α), (∀ X ∈ L, V.mem X) ∧ W = ⋃ X ∈ L, V.upSet X

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
