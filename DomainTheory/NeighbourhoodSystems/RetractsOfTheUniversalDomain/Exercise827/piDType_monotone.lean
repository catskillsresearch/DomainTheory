/-ai
The type of d at an element s lies below the type of d at any larger element.

The type map is monotone on elements, and passage from function-space elements to approximable maps preserves the resulting inequality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap






















































/-- **`piDType d` is monotone in `s`.** Composite of monotone `toElementMap`s (`d`, `subU`,
`jArrow`) followed by monotone `toApproxMap` (`Sub8_6.toApproxMap_monotone`). -/
theorem piDType_monotone (d : ApproximableMap U U) {s s' : U.Element} (h : s ≤ s') :
    piDType d s ≤ piDType d s' :=
  Sub8_6.toApproxMap_monotone ((piDTypeMap d).toElementMap_mono h)

end DomainTheory.NeighbourhoodSystems
