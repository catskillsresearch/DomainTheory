module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

section Tower

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- **Scott 1972, recursion before Theorem 4.4 (from Proposition 3.7).**
`j_{n+1}(x') = jₙ ∘ x' ∘ iₙ`. -/
theorem towerProj_succ_retr_apply (n : ℕ) (x' : towerType D₀ (n + 2)) (y : towerType D₀ n) :
    ((towerProj D₀ j₀ (n + 1)).retr x') y
      = (towerProj D₀ j₀ n).retr (x' ((towerProj D₀ j₀ n).incl y)) := rfl

end Tower

end DomainTheory.ContinuousLattice
