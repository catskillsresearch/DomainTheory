/-ai
stepFinSingle is the finite set of states reached in one step from a single state on one symbol. The universal language steps to every state, a singleton word steps by its deterministic automaton, and an intersection steps in each component. For a concatenation, a right state steps by the right injection of the second factor's step, and a left state steps by the left injection of the first factor's step, together with the right injection of the second factor's start set when that step meets an accept state of the first factor.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.acceptFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.startFin

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

/-- The step function of `toNFA e` from a single state, as a `Finset`. The `.cat` case's `inl`
branch mirrors `startFin`'s epsilon-closure handling exactly (one hop, on reaching an `a`-accept
state after the step). -/
def stepFinSingle : (e : SExpr) → autState e → Bool → Finset (autState e)
  | .sigma => fun _ _ => Finset.univ
  | .single σ => fun s c => {(singleDFA σ).step s c}
  | .cap a b => fun s c => (stepFinSingle a s.1 c) ×ˢ (stepFinSingle b s.2 c)
  | .cat a b => fun s c =>
      match s with
      | inl s' =>
          if ((stepFinSingle a s' c) ∩ (acceptFin a)).Nonempty
          then (stepFinSingle a s' c).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (stepFinSingle a s' c).image (inl : autState a → autState a ⊕ autState b)
      | inr s' => (stepFinSingle b s' c).image (inr : autState b → autState a ⊕ autState b)

end Exercise722

end DomainTheory.NeighbourhoodSystems
