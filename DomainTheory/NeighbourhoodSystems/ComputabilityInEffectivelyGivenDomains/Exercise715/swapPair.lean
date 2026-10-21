/-ai
Swapping a coded pair exchanges its two components.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

namespace ScottPresentation

variable {V : NeighborhoodSystem α} (P : ScottPresentation V)

def swapPair (t : ℕ) : ℕ := Nat.pair t.unpair.2 t.unpair.1

end ScottPresentation

end DomainTheory.NeighbourhoodSystems
