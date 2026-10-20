module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

/-- The accept states of `toNFA e`, as a `Finset`. -/
def acceptFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨σ.length, Nat.lt_succ_self _⟩ : SingleState σ)}
  | .cap a b => (acceptFin a) ×ˢ (acceptFin b)
  | .cat a b => (acceptFin b).image (inr : autState b → autState a ⊕ autState b)

end Exercise722

end DomainTheory.NeighbourhoodSystems
