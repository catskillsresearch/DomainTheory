module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf_embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf_projInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_sourceTopology_homeomorph
public import DomainTheory.ContinuousLattice.InverseLimits.proposition_4_1
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_isContinuousLattice

@[expose] public section


namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str


section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))


section Thm44d

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))


/-- The inverse pair Scott writes down in the proof of Theorem 4.4:
`i_∞ = embInfInf` and `j_∞ = projInfInf` satisfy `j_∞ ∘ i_∞ = id` and `i_∞ ∘ j_∞ = id`. -/
theorem theorem_4_4_inverses :
    (projInfInf D₀ j₀).comp (embInfInf D₀ j₀) = ScottMap.idMap ∧
    (embInfInf D₀ j₀).comp (projInfInf D₀ j₀) = ScottMap.idMap :=
  ⟨projInfInf_comp_embInfInf D₀ j₀, embInfInf_comp_projInfInf D₀ j₀⟩

/-- Lattice isomorphism along the same pair `i_∞`, `j_∞`. Scott's abstract also says the spaces
are isomorphic; this is not the statement of Theorem 4.4 (that statement is the homeomorphism). -/
noncomputable def theorem_4_4_orderIso : OrderIso (DInf D₀ j₀) (DInfFn D₀ j₀) :=
  (Equiv.mk (embInfInf D₀ j₀) (projInfInf D₀ j₀)
      (projInfInf_embInfInf D₀ j₀) (embInfInf_projInfInf D₀ j₀)).toOrderIso
    (embInfInf D₀ j₀).monotone (projInfInf D₀ j₀).monotone

/-- **Scott 1972, Theorem 4.4** (`sources/ScottContinLatt1972.md`):
*The inverse limit \(D_\infty\) of the recursively defined sequence
\(\langle D_n, j_n \rangle_{n=0}^{\infty}\) of function spaces is not only a
continuous lattice, but it is also homeomorphic to its own function space
\([D_\infty \to D_\infty]\).*  Here “inverse limit” carries Scott's subspace
topology from the Pi product, while the function space carries Definition 3.1's
pointwise/Pi-induced topology. -/
theorem theorem_4_4 (h₀ : ContinuousLattice D₀.carrier) :
    @ContinuousLattice (DInf D₀ j₀) inferInstance ∧
      Nonempty
        (@Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀)
          (inverseLimitTopology (towerType D₀) (towerProj D₀ j₀))
          (scottMapInducedPiTopology (DInf D₀ j₀) (DInf D₀ j₀))) := by
  have hTower : ∀ n, ContinuousLattice (towerType D₀ n) := by
    intro n
    induction n with
    | zero => exact h₀
    | succ n ih => exact theorem_3_3_isContinuousLattice ih ih
  refine ⟨proposition_4_1 (towerType D₀) (towerProj D₀ j₀) hTower, ?_⟩
  exact ⟨theorem_4_4_sourceTopology_homeomorph D₀ j₀ hTower⟩

end Thm44d
end LimitMaps
end DomainTheory.ContinuousLattice
