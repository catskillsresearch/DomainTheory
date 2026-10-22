module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

/-- Apply an element of `D_{n+1}` as a function `Dₙ → Dₙ` (definitional via `towerType_succ`). -/
instance towerCoeFun {D₀ : CLat.{u}} {n : ℕ} :
    CoeFun (towerType D₀ (n + 1)) (fun _ => towerType D₀ n → towerType D₀ n) where
  coe f := towerToMap f

end DomainTheory.ContinuousLattice
