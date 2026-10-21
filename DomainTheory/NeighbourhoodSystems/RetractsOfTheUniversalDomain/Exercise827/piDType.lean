/-ai
The type of d at an element s is the approximable map of the image of s under the type map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.BasicInst38
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piDTypeMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- The "type at `s`" itself, as an `ApproximableMap U U`. Always a finitary projection
(`isFinitaryProjection_piDType`, Step 4), for *any* `d` and `s`. -/
noncomputable def piDType (d : ApproximableMap U U) (s : U.Element) : ApproximableMap U U :=
  toApproxMap ((piDTypeMap d).toElementMap s)

end DomainTheory.NeighbourhoodSystems
