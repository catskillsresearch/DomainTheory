/-ai
Corresponding sets are nonempty together.

The correspondence is given by one formula. From a natural number in the evaluation on the natural numbers, the function of its bits lies in the Cantor-space evaluation, by the two membership bridges. From a point of the Cantor-space evaluation, some natural number matches that point, read as a valuation, on the variables of the formula; agreement of the two valuations and the two bridges put that number in the evaluation on the natural numbers.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_evalSet'_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.toSet'_mk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Corresponds

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- `Corresponds` matches `Set.Nonempty` — via `n ↦ fun i => n.testBit i` directly for `→`, and
`exists_bitsOf_agree` (`8.13(b)`) for `←`, since a formula's satisfying valuation can always be
swapped for a matching bit-derived one on its own (finite) variables. -/
theorem Corresponds.nonempty_iff {X : Set ℕ} {Y : Set (ℕ → Bool)} (h : Corresponds X Y) :
    X.Nonempty ↔ Y.Nonempty := by
  obtain ⟨φ, rfl, rfl⟩ := h
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨fun i => n.testBit i, (mem_evalSet'_iff _ φ).mpr ((mem_evalSet_iff n φ).mp hn)⟩
  · rintro ⟨v, hv⟩
    obtain ⟨n, hn⟩ := exists_bitsOf_agree (vars φ) v
    refine ⟨n, (mem_evalSet_iff n φ).mpr ?_⟩
    rw [evalV_eq_of_agree hn]
    exact (mem_evalSet'_iff v φ).mp hv

end DomainTheory.NeighbourhoodSystems
