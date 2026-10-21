/-ai
The strict lift of any value table sends bottom to bottom.

By extensionality of elements, a neighbourhood of the image is witnessed by an input belonging to bottom, hence equal to the whole space. The blunt clause makes the output the master of the codomain, so the output belongs to bottom there, while a singleton clause would make the whole space a singleton. Conversely, the master of the codomain belongs to its bottom, and the whole space belongs to bottom and is related to that master by the blunt clause.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.Basic
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
