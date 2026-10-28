module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid24

def lowerBoundEnt (u : Finset ℕ) (m : ℕ) : Prop :=
  m = 0 ∨ ∃ n ∈ u, m ≤ n

end Factoid24

end DomainTheory.InformationSystems
