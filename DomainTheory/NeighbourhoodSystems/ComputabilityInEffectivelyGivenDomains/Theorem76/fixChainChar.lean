/-ai
The chain characteristic of a function-space code and a list code is the fold of the packed fixed-point step, with that function-space code as parameter, starting from the pairing of the master index with 1, over the list coded by the list code. The result pairs the last index with a flag.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixStp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

variable (P : ComputablePresentation V)

/-- The chain `foldCode`: starts from `pair masterIdx 1`, threads the parameter `c`, over the list
coded by `i`. Returns `pair lastIdx flag`. -/
def fixChainChar (fincl : ℕ → ℕ) (c i : ℕ) : ℕ :=
  foldCode (fixStp fincl) c (Nat.pair P.masterIdx 1) i

end DomainTheory.NeighbourhoodSystems
