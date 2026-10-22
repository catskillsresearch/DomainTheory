module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

@[simp] theorem towerType_zero (D₀ : CLat.{u}) : towerType D₀ 0 = D₀.carrier := rfl

end DomainTheory.ContinuousLattice
