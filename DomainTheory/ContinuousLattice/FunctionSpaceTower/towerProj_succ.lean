/-ai
The successor of a tower projection has inclusion equal to conjugation by the inclusion and retraction of the previous level, and retraction equal to conjugation by the retraction and inclusion of the previous level.

Both equalities are definitional.
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str


theorem towerProj_succ (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier)) (n : ℕ) :
    let P := towerProj D₀ j₀ n
    (towerProj D₀ j₀ (n + 1)).incl = conjMap P.incl P.retr ∧
      (towerProj D₀ j₀ (n + 1)).retr = conjMap P.retr P.incl := by
  exact ⟨rfl, rfl⟩

end DomainTheory.ContinuousLattice
