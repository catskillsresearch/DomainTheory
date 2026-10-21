/-ai
The slot prefix of a tag i and an index j is the string consisting of the bit i, followed by j ones, followed by a zero. Reaching component j of the tag-i tuple means matching this prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- The slot prefix `i 1ʲ 0`: the leading tag bit `i` (Scott's `+/−`), then `j` ones, then a zero.
Reaching component `j` of the tag-`i` tuple means matching this prefix. -/
def slotPre (i : Bool) (j : ℕ) : Str := i :: (List.replicate j true ++ [false])

end Example62A
end DomainTheory.NeighbourhoodSystems
