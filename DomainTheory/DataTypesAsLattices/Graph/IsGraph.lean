/-ai
Scott's Theorem 1.2 (iii) takes a set u to be a graph when it is downward closed in the finite-set argument: if the pair of k and m lies in u and the basic element coded by k is contained in the basic element coded by n, then the pair of n and m lies in u.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.2 (iii).** Equality in (ii) iff `u` is downward
closed in the finite-set argument: `(k, m) ∈ u` and `e k ⊆ e n` imply `(n, m) ∈ u`. -/
def IsGraph (u : Pomega) : Prop :=
  ∀ ⦃k m n⦄, pair k m ∈ u → e k ⊆ e n → pair n m ∈ u

end DomainTheory.DataTypesAsLattices
