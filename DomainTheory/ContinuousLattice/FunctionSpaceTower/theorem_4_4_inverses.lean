module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_orderIso
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_sourceTopology_homeomorph

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

end Thm44d
end LimitMaps
end DomainTheory.ContinuousLattice
