module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitTopology
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_scottTopology_homeomorph
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_scottTopology_eq_induced_pi
public import DomainTheory.ContinuousLattice.InverseLimits.proposition_4_1
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_topology_induced_pi
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

/-- Scott's Theorem 4.4 homeomorphism with the literal topologies used in the source:
the inverse-limit subspace topology from the Pi product on `D∞`, and Definition 3.1's
pointwise (equivalently Pi-induced) topology on `[D∞ → D∞]`.

The topology changes are the mathematical identifications supplied by Proposition 4.1 and
Theorem 3.3; the underlying maps remain Scott's displayed `i∞` and `j∞` formulas above. -/
noncomputable def theorem_4_4_sourceTopology_homeomorph
    (hTower : ∀ n, ContinuousLattice (towerType D₀ n)) :
    @Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀)
      (inverseLimitTopology (towerType D₀) (towerProj D₀ j₀))
      (scottMapInducedPiTopology (DInf D₀ j₀) (DInf D₀ j₀)) := by
  have hDInf : ContinuousLattice (DInf D₀ j₀) :=
    proposition_4_1 (towerType D₀) (towerProj D₀ j₀) hTower
  rw [← inverseLimit_scottTopology_eq_induced_pi
        (towerType D₀) (towerProj D₀ j₀) hTower,
      ← theorem_3_3_topology_induced_pi hDInf hDInf]
  exact theorem_4_4_scottTopology_homeomorph D₀ j₀

end Thm44d

end LimitMaps

end DomainTheory.ContinuousLattice
