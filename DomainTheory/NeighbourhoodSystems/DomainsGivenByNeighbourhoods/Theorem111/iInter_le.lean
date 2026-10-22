module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `⋂ₙ xₙ ⊑ xₙ`: the intersection approximates every member of the sequence. -/
theorem iInter_le (x : ℕ → V.Element) (n : ℕ) : V.iInter x ≤ x n :=
  fun _ h => h n

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
