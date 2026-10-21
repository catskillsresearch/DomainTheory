/-ai
The reverse memo table equals the natural recursion that starts at zero and at each step pairs the step's value with the previous value and adds one.

At zero both sides are zero. At a successor the table equation matches the recursive clause by the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.rtbl

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem rtbl_eq_rec (step : ℕ → ℕ) (w : ℕ) :
    rtbl step w
      = Nat.rec (motive := fun _ => ℕ) 0
          (fun y IH => Nat.pair (step (Nat.pair y IH)) IH + 1) w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [rtbl, ih]

end Proposition77

end DomainTheory.NeighbourhoodSystems
