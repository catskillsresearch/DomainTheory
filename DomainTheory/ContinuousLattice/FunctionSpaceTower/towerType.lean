module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerCLat

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

/-- The carrier `Dₙ` of the function-space tower. -/
def towerType (D₀ : CLat.{u}) (n : ℕ) : Type u := (towerCLat D₀ n).carrier

end DomainTheory.ContinuousLattice
