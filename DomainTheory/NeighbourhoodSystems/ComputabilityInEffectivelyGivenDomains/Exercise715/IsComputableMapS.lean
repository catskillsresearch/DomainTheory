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

/-- **Definition 7.2 relative to bare presentations.** A computable map between bare presentations is
one whose neighbourhood relation `Xₙ f Yₘ` is r.e. (identical to `IsComputableMap`, which only uses
the enumerations). -/
def IsComputableMapS {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ScottPresentation V) (Q : ScottPresentation W) (f : ApproximableMap V W) : Prop :=
  REPred₂ (fun n m => f.rel (P.X n) (Q.X m))

end DomainTheory.NeighbourhoodSystems
