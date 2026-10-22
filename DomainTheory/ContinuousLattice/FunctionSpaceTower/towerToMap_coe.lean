module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

@[simp] theorem towerToMap_coe {D₀ : CLat.{u}} {n : ℕ} (f : towerType D₀ (n + 1))
    (x : towerType D₀ n) : towerToMap f x = f x := rfl

end DomainTheory.ContinuousLattice
