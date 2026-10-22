module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

/-- `denote e₁ ⊆ denote e₂`, decided by a bounded search: if no word up to the `diffNFA` state
bound witnesses `e₁ \ e₂`, none exists at all (`exists_diff_word_short`). -/
def subsetB (e1 e2 : SExpr) : Bool :=
  (wordsUpTo (Fintype.card (Finset (autState e1) × Finset (autState e2)))).all
    (fun w => !matchesB e1 w || matchesB e2 w)

end Exercise722

end DomainTheory.NeighbourhoodSystems
