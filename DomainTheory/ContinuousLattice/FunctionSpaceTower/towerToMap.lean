module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

/-- View an element of `D_{n+1}` as the Scott map `[Dₙ → Dₙ]` it definitionally is. -/
def towerToMap {D₀ : CLat.{u}} {n : ℕ} (f : towerType D₀ (n + 1)) :
    ScottMap (towerType D₀ n) (towerType D₀ n) := f

end DomainTheory.ContinuousLattice
