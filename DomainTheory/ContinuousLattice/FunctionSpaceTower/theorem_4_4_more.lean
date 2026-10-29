module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf_projInfInf
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitTopology
public import DomainTheory.ContinuousLattice.InverseLimits.proposition_4_1
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapInducedPiTopology

@[expose] public section

namespace DomainTheory.ContinuousLattice

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44d

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

noncomputable def theorem_4_4.scottTopology_homeomorph :
    @Homeomorph (DInf D₀ j₀) (DInf.fn D₀ j₀) scottTopologicalSpace scottTopologicalSpace :=
  @Homeomorph.mk (DInf D₀ j₀) (DInf.fn D₀ j₀) scottTopologicalSpace scottTopologicalSpace
    (Equiv.mk (embInfInf D₀ j₀) (projInfInf D₀ j₀)
      (projInfInf.embInfInf D₀ j₀) (embInfInf_projInfInf D₀ j₀))
    (embInfInf D₀ j₀).continuous (projInfInf D₀ j₀).continuous

end Thm44d

end LimitMaps

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44d

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

noncomputable def theorem_4_4.sourceTopology_homeomorph
    (hTower : ∀ n, ContinuousLattice (towerType D₀ n)) :
    @Homeomorph (DInf D₀ j₀) (DInf.fn D₀ j₀)
      (inverseLimitTopology (towerType D₀) (towerProj D₀ j₀))
      (scottMapInducedPiTopology (DInf D₀ j₀) (DInf D₀ j₀)) := by
  have hDInf : ContinuousLattice (DInf D₀ j₀) :=
    proposition_4_1 (towerType D₀) (towerProj D₀ j₀) hTower
  rw [← inverseLimit.scottTopology_eq_induced_pi
        (towerType D₀) (towerProj D₀ j₀) hTower,
      ← scottMapInducedPiTopology.scottTopology_eq_inducedPi hDInf hDInf]
  exact theorem_4_4.scottTopology_homeomorph D₀ j₀

end Thm44d

end LimitMaps

end DomainTheory.ContinuousLattice
