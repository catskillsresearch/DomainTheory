/-ai
If a doubly indexed set is a neighbourhood of the double iteration, then every double fiber of that set is a neighbourhood of the original system.

The neighbourhood data supply a neighbourhood of the iteration at the outer index, and that neighbourhood supplies a neighbourhood of the original system at the inner index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

/-- `V.mem (fiber2 S i j)` for every `(D^∞)^∞`-neighbourhood `S`. -/
theorem mem_fiber2_of_mem {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) (i j : ℕ) :
    V.mem (fiber2 S i j) := (hS.1 i).1 j

end Exercise718

end DomainTheory.NeighbourhoodSystems
