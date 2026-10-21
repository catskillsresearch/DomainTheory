/-ai
If the filter of one fixed point lies below the filter of another, then the underlying element of the first lies below the underlying element of the second.

Let a neighbourhood belong to the first element. The principal up-set of its compact generator lies in the first filter, hence in the second, so some compact below the second fixed point has the same up-set. Injectivity of up-sets identifies the two underlying elements. Inflation puts the principal element of the neighbourhood below the image of the generator, and that image lies below the second fixed point, so the neighbourhood belongs to the second element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.le_toElementMap_of_isClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.genK
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix_injOn
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.toElementFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)

theorem le_of_toElementFilter_le {y y' : FixSet a}
    (hle : toElementFilter h y ≤ toElementFilter h y') : y.1 ≤ y'.1 := by
  intro X hXy
  have hX : E.mem X := y.1.sub hXy
  have hky : (toElementFilter h y).mem (upFix h (genK h hX)) := by
    refine ⟨genK h hX, rfl, ?_⟩
    have h1 : E.principal hX ≤ y.1 := principal_le_of_mem hXy
    have h2 := a.toElementMap_mono h1
    rwa [y.2] at h2
  obtain ⟨k', hkk', hk'y'⟩ := hle _ hky
  have hkeq : (genK h hX).1.1 = k'.1.1 := upFix_injOn h hkk'
  have h1 : E.principal hX ≤ a.toElementMap (E.principal hX) :=
    le_toElementMap_of_isClosureOperator h _
  rw [show a.toElementMap (E.principal hX) = k'.1.1 from hkeq] at h1
  exact (h1.trans hk'y') X ((E.mem_principal hX).mpr ⟨hX, subset_rfl⟩)

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
