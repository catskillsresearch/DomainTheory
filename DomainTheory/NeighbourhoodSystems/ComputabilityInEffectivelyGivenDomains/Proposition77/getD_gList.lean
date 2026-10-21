/-ai
The entry at position p of the reverse memo list at w, for p strictly below w, is the course-of-values value at w minus one minus p.

The zero list has no such position. On a successor list, position zero is the head, which is the value at the predecessor, and a later position is the corresponding entry of the tail, shifted by one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gList

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem getD_gList (step : ℕ → ℕ) : ∀ (w p : ℕ), p < w →
    (gList step w).getD p 0 = gOf step (w - 1 - p) := by
  intro w
  induction w with
  | zero => intro p hp; omega
  | succ w ih =>
      intro p hp
      cases p with
      | zero =>
          rw [gList, List.getD_cons_zero]
          have : w + 1 - 1 - 0 = w := by omega
          rw [this]
      | succ p =>
          rw [gList, List.getD_cons_succ, ih p (by omega)]
          have : w + 1 - 1 - (p + 1) = w - 1 - p := by omega
          rw [this]

end Proposition77

end DomainTheory.NeighbourhoodSystems
