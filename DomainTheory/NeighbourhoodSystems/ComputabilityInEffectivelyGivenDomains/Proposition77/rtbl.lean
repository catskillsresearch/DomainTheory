/-ai
The reverse memo table of a step is zero at zero, and at a successor it is one more than the pair of the step at the pair of the predecessor and the previous table with that previous table.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The reverse memo table: `rtbl step w` codes `[g(w-1), …, g 0]`. -/
def rtbl (step : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (w + 1) => Nat.pair (step (Nat.pair w (rtbl step w))) (rtbl step w) + 1

end Proposition77

end DomainTheory.NeighbourhoodSystems
