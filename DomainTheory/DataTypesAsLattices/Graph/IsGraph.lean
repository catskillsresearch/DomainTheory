
module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.2 (iii).** Equality in (ii) iff `u` is downward
closed in the finite-set argument: `(k, m) ∈ u` and `e k ⊆ e n` imply `(n, m) ∈ u`. -/
class IsGraph (u : Pomega) : Prop where
  out : ∀ ⦃k m n⦄, pair k m ∈ u → e k ⊆ e n → pair n m ∈ u

end DomainTheory.DataTypesAsLattices
