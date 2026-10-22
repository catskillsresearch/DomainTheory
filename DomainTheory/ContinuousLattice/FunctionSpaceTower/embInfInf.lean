module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- **Scott 1972, §4 (Theorem 4.4).** The embedding `i_∞ : D_∞ → [D_∞ → D_∞]`,
`i_∞(x) = ⨆ₙ i_{n∞} ∘ x_{n+1} ∘ j_{∞n}`. It is Scott-continuous because it is a supremum of the
Scott maps `iInfTerm n` (suprema in `[D_∞ → [D_∞ → D_∞]]` are computed pointwise). -/
noncomputable def embInfInf : ScottMap (DInf D₀ j₀) (DInfFn D₀ j₀) :=
  ⨆ n, iInfTerm D₀ j₀ n

end LimitMaps

end DomainTheory.ContinuousLattice
