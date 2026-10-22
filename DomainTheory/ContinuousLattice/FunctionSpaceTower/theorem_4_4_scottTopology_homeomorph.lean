module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf_embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf_projInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic

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
