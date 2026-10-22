module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- `⊥ ∈ N` reads: a neighbourhood lies in `⊥` iff it is the whole space `ℕ`. -/
theorem N_bot_mem {X : Set ℕ} : N.bot.mem X ↔ X = Set.univ := NeighborhoodSystem.mem_bot N

end DomainTheory.NeighbourhoodSystems.Example43
