/-ai
If the starting lattice D_0 is a continuous lattice, then the inverse limit D_∞ of the recursively defined tower of function spaces is a continuous lattice, and D_∞ is homeomorphic to its function space [D_∞ → D_∞]. The inverse limit carries the subspace topology induced from the product, and the function space carries the pointwise topology of Definition 3.1.

Every level of the tower is a continuous lattice by induction on the level: the starting level is the hypothesis, and a successor level is a function space of continuous lattices, hence a continuous lattice by Theorem 3.3. Proposition 4.1 then makes the inverse limit a continuous lattice, and the source-topology form of the Theorem 4.4 homeomorphism supplies the homeomorphism.
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u


attribute [instance] CLat.str






















section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))














section Thm44d

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))






/-- **Scott 1972, Theorem 4.4** (`sources/ScottContinLatt1972.md`):
*The inverse limit \(D_\infty\) of the recursively defined sequence
\(\langle D_n, j_n \rangle_{n=0}^{\infty}\) of function spaces is not only a
continuous lattice, but it is also homeomorphic to its own function space
\([D_\infty \to D_\infty]\).*  Here “inverse limit” carries Scott's subspace
topology from the Pi product, while the function space carries Definition 3.1's
pointwise/Pi-induced topology. -/
theorem theorem_4_4 (h₀ : IsContinuousLattice D₀.carrier) :
    @IsContinuousLattice (DInf D₀ j₀) inferInstance ∧
      Nonempty
        (@Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀)
          (inverseLimitTopology (towerType D₀) (towerProj D₀ j₀))
          (scottMapInducedPiTopology (DInf D₀ j₀) (DInf D₀ j₀))) := by
  have hTower : ∀ n, IsContinuousLattice (towerType D₀ n) := by
    intro n
    induction n with
    | zero => exact h₀
    | succ n ih => exact theorem_3_3_isContinuousLattice ih ih
  refine ⟨proposition_4_1 (towerType D₀) (towerProj D₀ j₀) hTower, ?_⟩
  exact ⟨theorem_4_4_sourceTopology_homeomorph D₀ j₀ hTower⟩

end Thm44d
end LimitMaps
end DomainTheory.ContinuousLattice
