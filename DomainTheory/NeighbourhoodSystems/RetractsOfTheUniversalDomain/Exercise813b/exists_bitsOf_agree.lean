/-ai
For any finite set of coordinates and any valuation, some natural number has those bits equal to the valuation on that set.

Take the bitmask of the coordinates in the set at which the valuation is true. The bit test of that mask is true at a coordinate of the set exactly when the valuation is true there, by the bit test of a bitmask and membership in the filter. Comparing the two Boolean values in each of the four combinations gives the equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- Given any (finite) target set of variables and any valuation `v`, some `n : ℕ` matches `v` on
exactly that set — witnessed directly via `bitmaskOf` (`Exercise813a.lean`). -/
theorem exists_bitsOf_agree (S : Finset ℕ) (v : ℕ → Bool) :
    ∃ n : ℕ, ∀ i ∈ S, n.testBit i = v i := by
  refine ⟨bitmaskOf (S.filter (fun i => v i)), fun i hi => ?_⟩
  have key : (bitmaskOf (S.filter (fun i => v i))).testBit i = true ↔ v i = true := by
    rw [testBit_bitmaskOf]; simp [Finset.mem_filter, hi]
  rcases hv : v i with - | - <;> rcases hn : (bitmaskOf (S.filter (fun i => v i))).testBit i
    with - | - <;> simp_all

end DomainTheory.NeighbourhoodSystems
