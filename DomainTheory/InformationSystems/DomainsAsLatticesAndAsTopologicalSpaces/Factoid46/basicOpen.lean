/-ai
The basic open determined by a finite set of tokens is the set of elements whose carrier contains that set.
ai-/

module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.ScottContinuous

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- **Scott §4.** Basic open `[u] = {x ∈ |A| | u ⊆ x}`. -/
def basicOpen (A : InfoSys α) (u : Finset α) : Set A.Element :=
  {x | ↑u ⊆ x.carrier}

end InfoSys

end DomainTheory.InformationSystems
