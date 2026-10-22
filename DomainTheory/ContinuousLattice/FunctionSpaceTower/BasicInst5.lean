module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

noncomputable instance towerCompleteLattice (D₀ : CLat.{u}) (n : ℕ) :
    CompleteLattice (towerType D₀ n) := (towerCLat D₀ n).str

end DomainTheory.ContinuousLattice
