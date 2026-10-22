module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.BasicInst34
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.genFamily
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.genFamily_directed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- **`y` is the directed union of `a(↑X)` for `X ∈ y`.** Apply `a` (continuous, `toElementMap_
iSupDirected`) to `E`'s own algebraicity decomposition (`eq_iSupDirected_principal`) of `y.1`, then
use `a(y.1) = y.1`. -/
theorem toElementMap_eq_iSupDirected_genFamily (y : FixSet a) :
    y.1 = iSupDirected (fun i => (genFamily h y i).1) (genFamily_directed h y) := by
  have h1 : a.toElementMap y.1 = iSupDirected (fun i => (genFamily h y i).1) (genFamily_directed h y) := by
    conv_lhs => rw [eq_iSupDirected_principal y.1]
    exact toElementMap_iSupDirected a _ (principalFamily_directed y.1)
  rw [y.2] at h1
  exact h1

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
