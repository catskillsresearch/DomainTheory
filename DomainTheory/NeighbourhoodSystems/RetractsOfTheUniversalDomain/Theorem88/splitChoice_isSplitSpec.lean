/-ai
The total splitting choice satisfies the splitting specification.

Under the hypotheses of the specification the conditional takes the chosen branch, and the chosen pair satisfies the existential conclusion of the splitting step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
import all Mathlib.Data.Fintype.Pi
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}







open Classical in



open Classical in

theorem splitChoice_isSplitSpec : SplitSpec (α := α) splitChoice := by
  intro A B hAB hBU Xn
  classical
  unfold splitChoice
  rw [dite_eq_left ⟨hAB, hBU⟩]
  exact (exists_split hAB hBU Xn).choose_spec.choose_spec

end DomainTheory.NeighbourhoodSystems
