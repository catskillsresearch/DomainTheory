module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_orderIso
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_sourceTopology_homeomorph

@[expose] public section


namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str


section Tower

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- **Scott 1972, recursion before Theorem 4.4 (from Proposition 3.7).**
`i_{n+1}(x) = iₙ ∘ x ∘ jₙ`. -/
theorem towerProj_succ_incl_apply (n : ℕ) (x : towerType D₀ (n + 1)) (y : towerType D₀ (n + 1)) :
    ((towerProj D₀ j₀ (n + 1)).incl x) y
      = (towerProj D₀ j₀ n).incl (x ((towerProj D₀ j₀ n).retr y)) := rfl

end Tower
end DomainTheory.ContinuousLattice
