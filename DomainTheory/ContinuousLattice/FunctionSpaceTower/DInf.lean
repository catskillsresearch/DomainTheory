module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : ContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

abbrev DInf : Type u := InverseLimit (towerType D₀) (towerProj D₀ j₀)

namespace DInf

abbrev fn : Type u := ScottMap (DInf D₀ j₀) (DInf D₀ j₀)

end DInf

end LimitMaps

end DomainTheory.ContinuousLattice
