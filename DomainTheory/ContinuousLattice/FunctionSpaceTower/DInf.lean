module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

abbrev DInf : Type u := InverseLimit (towerType D₀) (towerProj D₀ j₀)

end LimitMaps

end DomainTheory.ContinuousLattice
