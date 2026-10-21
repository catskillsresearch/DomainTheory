/-ai
The flat relation holds between finite sets u and v when 1 belongs to u, or every token of v equals 0 or belongs to u and 1 does not belong to v.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

/-- If `1 ∈ u`, accept any `v`; else require `v ⊆ u ∪ {0}` and `1 ∉ v`. -/
def flatRel (u v : Finset ℕ) : Prop :=
  (1 ∈ u) ∨ ((∀ n ∈ v, n = 0 ∨ n ∈ u) ∧ 1 ∉ v)

end Factoid84

end DomainTheory.InformationSystems
