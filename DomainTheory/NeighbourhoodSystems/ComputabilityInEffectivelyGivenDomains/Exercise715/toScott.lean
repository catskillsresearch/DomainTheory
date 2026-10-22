module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

/-- A full (`inter`-carrying) presentation forgets to a bare one. Hence the project's
`IsEffectivelyGiven` implies Scott's `IsEffectivelyGivenS`. -/
def ComputablePresentation.toScott {V : NeighborhoodSystem α} (P : ComputablePresentation V) :
    ScottPresentation V where
  X := P.X
  mem_X := P.mem_X
  surj := P.surj
  interEq_computable := P.interEq_computable
  cons_computable := P.cons_computable

end DomainTheory.NeighbourhoodSystems
