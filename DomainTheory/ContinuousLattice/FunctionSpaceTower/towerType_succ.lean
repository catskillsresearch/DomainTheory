module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_orderIso
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.theorem_4_4_sourceTopology_homeomorph

@[expose] public section


namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str


/-- `D_{n+1}` is *definitionally* the function space `[Dₙ → Dₙ]`. -/
theorem towerType_succ (D₀ : CLat.{u}) (n : ℕ) :
    towerType D₀ (n + 1) = ScottMap (towerType D₀ n) (towerType D₀ n) := rfl

end DomainTheory.ContinuousLattice
