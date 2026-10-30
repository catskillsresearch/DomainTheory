module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm
public import DomainTheory.ContinuousLattice.ScottMaps.proposition_2_5
public import Mathlib.Data.Set.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : ContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

noncomputable def embInfInf : ScottMap (DInf D₀ j₀) (DInf.fn D₀ j₀) :=
  ⨆ n, iInfTerm D₀ j₀ n

namespace embInfInf

theorem apply (x : DInf D₀ j₀) :
    embInfInf D₀ j₀ x = ⨆ n, iInfTerm D₀ j₀ n x := by
  show (sSup (Set.range (iInfTerm D₀ j₀)) : ScottMap _ _) x = _
  rw [ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
  rfl

theorem preservesDirectedSup :
    PreservesDirectedSup (embInfInf D₀ j₀ : DInf D₀ j₀ → DInf.fn D₀ j₀) :=
  (proposition_2_5 _).mp (embInfInf D₀ j₀).continuous

end embInfInf

end LimitMaps

end DomainTheory.ContinuousLattice
