module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.isCompactFix_toElementMap_principal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- The generator of a compact fixed point from an `E`-neighbourhood `X`. -/
def genK {X : Set α} (hX : E.mem X) : CompactFix h :=
  ⟨⟨a.toElementMap (E.principal hX), toElementMap_idem h.out.1 _⟩,
    isCompactFix_toElementMap_principal h hX⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
