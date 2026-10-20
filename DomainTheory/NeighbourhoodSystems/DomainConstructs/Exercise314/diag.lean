module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 3.14 (Scott 1981, PRG-19).** The *diagonal* approximable mapping
`diag : 𝒟 → 𝒟 × 𝒟`, defined as the paired map `⟨I_𝒟, I_𝒟⟩` of the identity with itself. -/
def diag : ApproximableMap V (prod V V) := paired (idMap V) (idMap V)

end DomainTheory.NeighbourhoodSystems
