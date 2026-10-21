/-ai
acceptFin is the finite set of accept states of the automaton of an expression. It is every state for the universal language, the singleton of the final index for a singleton word, the product of the accept sets for an intersection, and the right injection of the second factor's accept set for a concatenation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide

@[expose] public section

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
