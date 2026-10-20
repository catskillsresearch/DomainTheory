module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- Minimal entailment on `ℕ` with `0 = Δ`: `u ⊢ n` iff `n = 0` or `n ∈ u`. -/
def PEnt (u : Finset ℕ) (n : ℕ) : Prop :=
  n = 0 ∨ n ∈ u

end Factoid84

end DomainTheory.InformationSystems
