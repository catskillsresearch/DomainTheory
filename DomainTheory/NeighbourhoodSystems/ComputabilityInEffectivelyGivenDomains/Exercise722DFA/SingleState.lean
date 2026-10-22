module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.sigmaDFA_accepts

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

/-- States of the single-word DFA for `σ`: `some i` means "the input so far is the length-`i` prefix
of `σ`" (`i ≤ |σ|`); `none` is the dead/sink state (input has diverged from `σ`). -/
abbrev SingleState (σ : List Bool) : Type := Option (Fin (σ.length + 1))

end Exercise722

end DomainTheory.NeighbourhoodSystems
