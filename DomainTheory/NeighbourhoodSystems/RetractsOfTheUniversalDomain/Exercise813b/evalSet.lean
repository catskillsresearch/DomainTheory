module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- The *same* recursion, but interpreted in `Set ℕ` via `generator` (`Exercise813a.lean`) instead
of an abstract Boolean — i.e. the specific homomorphism `var i ↦ generator i`. -/
def evalSet : Formula → Set ℕ
  | .var i => generator i
  | .bot => ∅
  | .top => Set.univ
  | .neg φ => (evalSet φ)ᶜ
  | .and φ ψ => evalSet φ ∩ evalSet ψ
  | .or φ ψ => evalSet φ ∪ evalSet ψ

end DomainTheory.NeighbourhoodSystems
