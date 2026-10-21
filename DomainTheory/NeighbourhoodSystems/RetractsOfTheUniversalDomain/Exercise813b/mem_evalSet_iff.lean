/-ai
A natural number lies in the evaluation set of a formula if and only if the formula is true under the valuation that reads the bits of that number.

The proof is by induction on the formula. At a variable, at falsehood, and at truth, the two sides simplify to the same condition. At a negation, conjunction, or disjunction, the inductive hypotheses match the set operations with the Boolean operations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- **The bridge between the two evaluations**: `evalSet` at `n : ℕ` agrees with `evalV` at `n`'s
own bit-sequence `fun i => n.testBit i`. -/
theorem mem_evalSet_iff (n : ℕ) (φ : Formula) :
    n ∈ evalSet φ ↔ evalV (fun i => n.testBit i) φ = true := by
  induction φ with
  | var i => simp [evalSet, evalV]
  | bot => simp [evalSet, evalV]
  | top => simp [evalSet, evalV]
  | neg φ ih => simp [evalSet, evalV, ih]
  | and φ ψ ihφ ihψ => simp [evalSet, evalV, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [evalSet, evalV, ihφ, ihψ]

end DomainTheory.NeighbourhoodSystems
