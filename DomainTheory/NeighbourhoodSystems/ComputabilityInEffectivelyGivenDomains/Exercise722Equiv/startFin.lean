/-ai
startFin is the finite set of start states of the automaton of an expression. It is every state for the universal language, the singleton of the initial index for a singleton word, and the product of the start sets for an intersection. For a concatenation it is the left injection of the first factor's start set, together with the right injection of the second factor's start set when some start state of the first factor is already accepting.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.acceptFin

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

/-- The start states of `toNFA e`, as a `Finset`. The `.cat` case handles the one-hop
ε-closure directly (`catEps`'s only ε-edges go from an `M₁`-accept state to `M₂`-start states,
`catEps_mem_εClosure_iff`): if some start state of `a` is already accepting, `b`'s start states
are also immediately live. -/
def startFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨0, Nat.succ_pos _⟩ : SingleState σ)}
  | .cap a b => (startFin a) ×ˢ (startFin b)
  | .cat a b =>
      if ((startFin a) ∩ (acceptFin a)).Nonempty
      then (startFin a).image (inl : autState a → autState a ⊕ autState b) ∪
        (startFin b).image (inr : autState b → autState a ⊕ autState b)
      else (startFin a).image (inl : autState a → autState a ⊕ autState b)

end Exercise722

end DomainTheory.NeighbourhoodSystems
