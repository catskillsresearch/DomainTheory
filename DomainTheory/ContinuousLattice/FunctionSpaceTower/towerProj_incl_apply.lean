module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj_succ_incl_apply

@[expose] public section


namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str


section Tower

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))


/-- **Scott 1972, §4 (application is preserved).** `iₙ(f(x)) = i_{n+1}(f)(iₙ(x))` for `f ∈ D_{n+1}`,
`x ∈ Dₙ`. The embeddings turn functional application into application one level up. -/
theorem towerProj_incl_apply (n : ℕ) (f : towerType D₀ (n + 1)) (x : towerType D₀ n) :
    (towerProj D₀ j₀ n).incl (f x)
      = ((towerProj D₀ j₀ (n + 1)).incl f) ((towerProj D₀ j₀ n).incl x) := by
  rw [towerProj_succ_incl_apply, (towerProj D₀ j₀ n).retr_incl]

end Tower
end DomainTheory.ContinuousLattice
