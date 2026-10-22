/-ai
The matcher accepts a word if and only if the word lies in the denotation of the expression.

Induction on the expression, generalizing the word. The universal language and a singleton reduce by the definitions. For concatenation, membership in a concatenation is a split of the word, and the search over cut points matches the inductive hypotheses in both directions, transporting the strict range bound across the successor comparison. For intersection, the conjunction of the two matcher calls matches the conjunction of the inductive hypotheses under the intersection equation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.mem_concat_iff_split
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.matchesB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- **The matcher is correct**: `matchesB e w = true ↔ w ∈ denote e`. By structural induction on `e`;
the concatenation case unfolds `List.any` over the cut points and applies `mem_concat_iff_split`. -/
theorem matchesB_iff (e : SExpr) (w : List Bool) : matchesB e w = true ↔ w ∈ denote e := by
  induction e generalizing w with
  | sigma => simp [matchesB]
  | single σ => simp [matchesB]
  | cat a b iha ihb =>
    rw [denote_cat, mem_concat_iff_split]
    simp only [matchesB, List.any_eq_true, List.mem_range, Bool.and_eq_true]
    constructor
    · rintro ⟨i, hi, ha, hb⟩
      exact ⟨i, Nat.lt_succ_iff.mp hi, (iha _).mp ha, (ihb _).mp hb⟩
    · rintro ⟨i, hi, ha, hb⟩
      exact ⟨i, Nat.lt_succ_iff.mpr hi, (iha _).mpr ha, (ihb _).mpr hb⟩
  | cap a b iha ihb =>
    simp only [matchesB, Bool.and_eq_true, denote_cap, Set.mem_inter_iff]
    rw [iha, ihb]

end Exercise722

end DomainTheory.NeighbourhoodSystems
