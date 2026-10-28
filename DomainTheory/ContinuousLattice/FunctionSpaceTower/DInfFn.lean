module

public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

abbrev DInfFn : Type u := ScottMap (DInf D₀ j₀) (DInf D₀ j₀)

end LimitMaps

end DomainTheory.ContinuousLattice
