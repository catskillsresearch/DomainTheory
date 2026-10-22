module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The two-term sequence `⟨U, W⟩` as a function `ℕ → Set α` (used to phrase `Consistent`). -/
def pairSeq (U W : Set α) : ℕ → Set α := fun i => if i = 0 then U else W

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
