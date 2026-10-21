/-ai
Occupancy test of (5.13). If both square components of u are inhabited, applying the boxed sum of a and b to u yields the full set, by the mixed test (4.4).

Members of the two components make the occupancy tags the singletons zero and one. The double conditional of a test containing both zero and a positive integer is the full set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.exists_mem_of_ne_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxTag_of_mem
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Occupancy test of (5.13): both components inhabited, so (4.4) gives `⊤`. -/
theorem boxPlus_app_mixed {a b u : Pomega} (hx : squareFst u ≠ botElem)
    (hy : squareSnd u ≠ botElem) :
    funOf (boxPlus a b) u = topElem := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hx
  obtain ⟨k, hk⟩ := exists_mem_of_ne_bot hy
  rw [boxPlus_app, boxTag_of_mem hm, boxTag_of_mem hk]
  exact dcondSet_of_mixed (by simp [ofNat]) ⟨0, by simp [ofNat]⟩

end DomainTheory.DataTypesAsLattices
