module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.ScottMaps.proposition_2_5

@[expose] public section


namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str


section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))


/-- `i_∞` is Scott-continuous (it is a bundled `ScottMap`). -/
theorem embInfInf_preservesDirectedSup :
    PreservesDirectedSup (embInfInf D₀ j₀ : DInf D₀ j₀ → DInfFn D₀ j₀) :=
  (proposition_2_5 _).mp (embInfInf D₀ j₀).continuous

end LimitMaps
end DomainTheory.ContinuousLattice
