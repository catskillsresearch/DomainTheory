/-ai
A state of the automaton for a single word is either an index at most the length of the word, recording that the input read so far is the prefix of that length, or a sink, recording that the input has left the word.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
import all Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
import all Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.sigmaDFA_accepts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

/-- States of the single-word DFA for `σ`: `some i` means "the input so far is the length-`i` prefix
of `σ`" (`i ≤ |σ|`); `none` is the dead/sink state (input has diverged from `σ`). -/
abbrev SingleState (σ : List Bool) : Type := Option (Fin (σ.length + 1))

end Exercise722

end DomainTheory.NeighbourhoodSystems
