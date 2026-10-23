module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- **Scott 1972, Proposition 2.2(i).** `⊥ ≪ x` for every `x`. -/
theorem bot_wayBelow (x : D) : (⊥ : D) ≪ x :=
  ⟨Set.univ, ScottOpen.univ, Set.mem_univ x, fun _ _ => bot_le⟩

end DomainTheory.ContinuousLattice
