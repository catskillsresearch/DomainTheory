/-ai
The reverse memo table at w is the code of the reverse memo list at w.

At zero both sides are zero. At a successor, the table is one more than the pair of the step at the previous table, and the list code is the code of the course-of-values value consed onto the previous list, which agrees by the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gList

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem rtbl_eq_encode (step : ℕ → ℕ) (w : ℕ) : rtbl step w = encodeList (gList step w) := by
  induction w with
  | zero => rfl
  | succ w ih =>
      show Nat.pair (step (Nat.pair w (rtbl step w))) (rtbl step w) + 1
        = encodeList (gList step (w + 1))
      rw [gList, encodeList, gOf, ih]

end Proposition77

end DomainTheory.NeighbourhoodSystems
