module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.natElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroElt
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.succMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.univ_ne_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_ne_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_nat_inj
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.T
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_bot_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- **Computation on bottom (strictness).** `f(⊥) = ⊥`. -/
theorem constLiftN_bot {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) :
    (constLiftN V val).toElementMap N.bot = V.bot := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXmem, hrel⟩
    rw [N_bot_mem] at hXmem
    subst hXmem
    rcases hrel with ⟨_, rfl⟩ | ⟨k, hXk, _⟩
    · exact V.mem_bot.mpr rfl
    · exact (univ_ne_singleton k hXk).elim
  · intro hY
    rw [V.mem_bot] at hY
    subst hY
    exact ⟨Set.univ, N_bot_mem.mpr rfl, Or.inl ⟨rfl, rfl⟩⟩

end DomainTheory.NeighbourhoodSystems.Example43
