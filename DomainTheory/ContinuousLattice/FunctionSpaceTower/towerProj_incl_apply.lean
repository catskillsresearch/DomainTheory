/-ai
Application is preserved by the tower embeddings: for f in D_{n+1} and x in D_n, the level-n embedding of f(x) equals the level-(n+1) embedding of f applied to the level-n embedding of x.

The successor formula for the inclusion expands the right-hand side as the level-n embedding of f applied to the retraction of the level-n embedding of x, and the retraction law cancels that retraction against the embedding.
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj_succ_incl_apply

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u


attribute [instance] CLat.str




















section Tower

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))


/-- **Scott 1972, §4 (application is preserved).** `iₙ(f(x)) = i_{n+1}(f)(iₙ(x))` for `f ∈ D_{n+1}`,
`x ∈ Dₙ`. The embeddings turn functional application into application one level up. -/
theorem towerProj_incl_apply (n : ℕ) (f : towerType D₀ (n + 1)) (x : towerType D₀ n) :
    (towerProj D₀ j₀ n).incl (f x)
      = ((towerProj D₀ j₀ (n + 1)).incl f) ((towerProj D₀ j₀ n).incl x) := by
  rw [towerProj_succ_incl_apply, (towerProj D₀ j₀ n).retr_incl]

end Tower
end DomainTheory.ContinuousLattice
