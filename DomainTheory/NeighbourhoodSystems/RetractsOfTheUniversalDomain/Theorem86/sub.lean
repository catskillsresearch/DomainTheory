module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Theorem 8.6's combinator `sub(f)` (Scott 1981, PRG-19), per token `f`.** Scott's formula
`X sub(f) Z ↔ ∃Y ∈ E, X⊆Y ∧ f.rel Y Y ∧ Y⊆Z` is literally `retractionOfSubsystem` applied to
`fixedNbhd f = {Y ∈ E ∣ Y f Y}` (Theorem 8.5's subsystem, built for *any* `f`). -/
def sub (f : ApproximableMap E E) : ApproximableMap E E :=
  Subsystem.retractionOfSubsystem (fixedNbhd_subsystem f)

end DomainTheory.NeighbourhoodSystems
