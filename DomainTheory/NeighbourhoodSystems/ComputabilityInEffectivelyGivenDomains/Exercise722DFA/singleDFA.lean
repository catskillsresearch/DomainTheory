/-ai
The automaton for a single word starts at length zero. From a length still inside the word, the matching next letter advances the length by one and any other letter goes to the sink. Once the word has been consumed, every letter goes to the sink. The only accept state is the length equal to the length of the word.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
import all Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
import all Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.sigmaDFA_accepts
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.SingleState

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

/-- The single-word DFA recognising `{σ}`. From `some i` (`i < |σ|`) reading the correct next
character advances to `some (i+1)`; any mismatch — or any character once `σ` is fully consumed — goes
to the dead state `none`. -/
def singleDFA (σ : List Bool) : DFA Bool (SingleState σ) where
  step s b := s.bind fun i =>
    if h : (i : ℕ) < σ.length then
      if σ.get ⟨i, h⟩ = b then some ⟨i + 1, by omega⟩ else none
    else none
  start := some ⟨0, by omega⟩
  accept := {some ⟨σ.length, by omega⟩}

end Exercise722

end DomainTheory.NeighbourhoodSystems
