module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- The standard truth-valuation semantics: `v : ℕ → Bool` assigns each variable a truth value. -/
def evalV (v : ℕ → Bool) : Formula → Bool
  | .var i => v i
  | .bot => false
  | .top => true
  | .neg φ => !(evalV v φ)
  | .and φ ψ => evalV v φ && evalV v ψ
  | .or φ ψ => evalV v φ || evalV v ψ

end DomainTheory.NeighbourhoodSystems
