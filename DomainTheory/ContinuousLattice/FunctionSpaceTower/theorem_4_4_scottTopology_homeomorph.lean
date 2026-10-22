/-ai
The pair i_∞ and j_∞ from the proof of Theorem 4.4 is a homeomorphism when both D_∞ and [D_∞ → D_∞] carry the Scott lattice topology. The embedding is i_∞(x) = ⨆_n (i_{n∞} ∘ x_{n+1} ∘ j_{∞n}) and the projection is j_∞(f) = ⨆_n i_{(n+1)∞}(j_{∞n} ∘ f ∘ i_{n∞}). The underlying equivalence is inverse by the two composite identities, and both maps are continuous. The homeomorphism for the source topologies of the numbered theorem is a separate construction.
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInfFn
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf_embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf_projInfInf

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44d

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- The pair \(i_\infty, j_\infty\) from the proof of Theorem 4.4, first packaged using the
Scott lattice topologies on both sides.  Scott writes
`i∞(x) = ⨆ₙ (i_{n∞} ∘ x_{n+1} ∘ j_{∞n})` and
`j∞(f) = ⨆ₙ i_{(n+1)∞}(j_{∞n} ∘ f ∘ i_{n∞})`, and says
(`sources/ScottContinLatt1972.md`): “We can write down directly the pair of maps
`i∞, j∞` that provide the homeomorphism.”

This helper is deliberately distinct from the source-topology homeomorphism in the numbered
theorem below. -/
noncomputable def theorem_4_4_scottTopology_homeomorph :
    @Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀) scottTopologicalSpace scottTopologicalSpace :=
  @Homeomorph.mk (DInf D₀ j₀) (DInfFn D₀ j₀) scottTopologicalSpace scottTopologicalSpace
    (Equiv.mk (embInfInf D₀ j₀) (projInfInf D₀ j₀)
      (projInfInf_embInfInf D₀ j₀) (embInfInf_projInfInf D₀ j₀))
    (embInfInf D₀ j₀).continuous (projInfInf D₀ j₀).continuous

end Thm44d

end LimitMaps

end DomainTheory.ContinuousLattice
