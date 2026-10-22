/-ai
For elements x and y of the inverse limit D_∞, the embedding i_∞ satisfies i_∞(x) ≤ i_∞(y) if and only if x ≤ y.

If i_∞(x) ≤ i_∞(y), monotonicity of the projection j_∞ and the identity j_∞ ∘ i_∞ = id return x ≤ y. In the other direction, monotonicity of i_∞ sends x ≤ y to i_∞(x) ≤ i_∞(y).
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str


section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))


section Thm44d

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))


theorem embInfInf_le_iff (x y : DInf D₀ j₀) :
    embInfInf D₀ j₀ x ≤ embInfInf D₀ j₀ y ↔ x ≤ y := by
  constructor
  · intro h
    have := (projInfInf D₀ j₀).monotone h
    rwa [projInfInf_embInfInf, projInfInf_embInfInf] at this
  · intro h; exact (embInfInf D₀ j₀).monotone h

end Thm44d
end LimitMaps
end DomainTheory.ContinuousLattice
