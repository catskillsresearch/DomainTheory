/-ai
If a neighbourhood system is effectively given, then it is effectively given in Scott's sense.

Eliminate the given computable presentation and take its underlying Scott presentation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


theorem NeighborhoodSystem.IsEffectivelyGiven.toS {V : NeighborhoodSystem α}
    (h : V.IsEffectivelyGiven) : V.IsEffectivelyGivenS :=
  h.elim fun P => ⟨P.toScott⟩

end DomainTheory.NeighbourhoodSystems
