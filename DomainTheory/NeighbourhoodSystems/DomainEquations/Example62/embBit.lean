/-ai
The tagging of a set of binary strings by a boolean is the set of strings that begin with that boolean and whose remaining suffix lies in the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- `bX = {b :: w' ∣ w' ∈ X}`: the `b`-prefixed copy of a neighbourhood `X` (Scott's `0X` for
`b = false` and `1X` for `b = true`). -/
def embBit (b : Bool) (X : Set Str) : Set Str := {w | ∃ w', w = b :: w' ∧ w' ∈ X}

end Example62

end DomainTheory.NeighbourhoodSystems
