/-ai
A neighbourhood system is effectively given in Scott's sense when it has a Scott presentation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

/-- **Effectively given (Scott's literal Definition 7.1).** -/
def NeighborhoodSystem.IsEffectivelyGivenS (V : NeighborhoodSystem α) : Prop :=
  Nonempty (ScottPresentation V)

end DomainTheory.NeighbourhoodSystems
