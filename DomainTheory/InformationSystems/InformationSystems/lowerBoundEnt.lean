/-ai
In the lower-bound system, a finite set of natural numbers entails m when m is zero or some member of the set is at least m.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid24

/-- Entailment for the lower-bound system: `u ⊢ m` iff `m = 0` or some `n ∈ u` has `m ≤ n`. -/
def lowerBoundEnt (u : Finset ℕ) (m : ℕ) : Prop :=
  m = 0 ∨ ∃ n ∈ u, m ≤ n

end Factoid24

end DomainTheory.InformationSystems
