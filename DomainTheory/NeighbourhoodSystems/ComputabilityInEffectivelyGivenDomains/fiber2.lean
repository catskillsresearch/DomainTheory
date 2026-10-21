/-ai
The double fiber of a doubly indexed set of tokens, at an outer index and an inner index, is the fiber at the inner index of the fiber of the set at the outer index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

/-- The **double-indexed fiber** of a `(D^∞)^∞`-set: `fiber2 S i j = fiber (fiber S i) j`, the tokens
`a` with `(i, (j, a)) ∈ S`. -/
def fiber2 (S : Set (ℕ × (ℕ × α))) (i j : ℕ) : Set α := fiber (fiber S i) j

end Exercise718

end DomainTheory.NeighbourhoodSystems
