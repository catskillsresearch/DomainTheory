/-ai
Two formulas are semantically equivalent if and only if they have the same evaluation set.

If they agree under every valuation, extending a natural number and rewriting membership by the bit bridge shows that the two evaluation sets contain the same numbers. Conversely, given a valuation, some natural number matches it on the variables of either formula. Agreement on those variables identifies each truth value with the value under the bits of that number, and equality of the evaluation sets makes those two bit-values true together. Comparing the four combinations of Boolean values gives equality of the original truth values.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.vars
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.mem_evalSet_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV_eq_of_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.exists_bitsOf_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.SemanticEquiv
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.formulaSetoid

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- **The one substantive lemma**: semantic equivalence (quantifying over *all* valuations) agrees
with `evalSet`-equality (which only ever "tests" the countably many bit-derived valuations) —
because a formula only mentions finitely many variables, any valuation can be swapped for a
matching bit-derived one on the (finite) variables that actually occur. -/
theorem semanticEquiv_iff_evalSet_eq {φ ψ : Formula} :
    SemanticEquiv φ ψ ↔ evalSet φ = evalSet ψ := by
  constructor
  · intro h
    ext n
    rw [mem_evalSet_iff, mem_evalSet_iff, h]
  · intro h v
    obtain ⟨n, hn⟩ := exists_bitsOf_agree (vars φ ∪ vars ψ) v
    have h1 : evalV v φ = evalV (fun i => n.testBit i) φ :=
      evalV_eq_of_agree fun i hi => (hn i (Finset.mem_union_left _ hi)).symm
    have h2 : evalV v ψ = evalV (fun i => n.testBit i) ψ :=
      evalV_eq_of_agree fun i hi => (hn i (Finset.mem_union_right _ hi)).symm
    have hiff : evalV (fun i => n.testBit i) φ = true ↔ evalV (fun i => n.testBit i) ψ = true := by
      rw [← mem_evalSet_iff, ← mem_evalSet_iff, h]
    rw [h1, h2]
    rcases hφ : evalV (fun i => n.testBit i) φ with - | - <;>
      rcases hψ : evalV (fun i => n.testBit i) ψ with - | - <;> simp_all

end DomainTheory.NeighbourhoodSystems
