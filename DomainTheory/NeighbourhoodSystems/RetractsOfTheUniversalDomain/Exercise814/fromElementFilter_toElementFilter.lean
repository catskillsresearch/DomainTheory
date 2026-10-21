/-ai
The composite of the backward map after the forward map is the identity on fixed points of a closure operator.

The underlying elements agree by antisymmetry. The directed supremum of the confirmed compacts lies below the fixed point, because injectivity of principal up-sets turns each confirmation into that inequality. In the other direction the fixed point is the directed supremum of its generating family, and each member of that family is a confirmed compact: the principal element of the corresponding neighbourhood lies below the fixed point, so monotonicity of the element map and the fixed-point equation put its image below the fixed point as well.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.genK
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix_injOn
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.toElementFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.confirmedIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.BasicInst34
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.confirmedIdx_directed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.fromElementFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.toElementMap_eq_iSupDirected_genFamily
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)

theorem fromElementFilter_toElementFilter (y : FixSet a) :
    fromElementFilter h (toElementFilter h y) = y := by
  apply Subtype.ext
  show iSupDirected (fun i : confirmedIdx h (toElementFilter h y) => i.1.1.1)
      (confirmedIdx_directed h (toElementFilter h y)) = y.1
  apply le_antisymm
  · apply iSupDirected_le
    rintro ⟨k, k', hkk', hk'y⟩
    exact (upFix_injOn h hkk' ▸ hk'y : k.1.1 ≤ y.1)
  · rw [toElementMap_eq_iSupDirected_genFamily h y]
    apply iSupDirected_le
    intro i
    have hk : (toElementFilter h y).mem (upFix h (genK h (y.1.sub i.2))) := by
      refine ⟨genK h (y.1.sub i.2), rfl, ?_⟩
      have h1 : E.principal (y.1.sub i.2) ≤ y.1 := principal_le_of_mem i.2
      have h2 := a.toElementMap_mono h1
      rwa [y.2] at h2
    exact le_iSupDirected (fun i : confirmedIdx h (toElementFilter h y) => i.1.1.1)
      (confirmedIdx_directed h (toElementFilter h y)) ⟨genK h (y.1.sub i.2), hk⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
