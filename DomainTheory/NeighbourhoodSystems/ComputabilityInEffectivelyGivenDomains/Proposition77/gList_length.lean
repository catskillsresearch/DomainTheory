/-ai
The reverse memo list of a step at w has length w.

At zero the list is empty. At a successor the list is a cons, so the length is one more than the inductive length.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem gList_length (step : ℕ → ℕ) (w : ℕ) : (gList step w).length = w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [gList, List.length_cons, ih]

end Proposition77
end DomainTheory.NeighbourhoodSystems
