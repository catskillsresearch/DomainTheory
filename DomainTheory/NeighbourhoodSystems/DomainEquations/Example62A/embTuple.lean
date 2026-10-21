/-ai
The tag-i tuple embTuple i X is the set of strings that begin with the slot prefix of some index j and continue with a string from the component X j. The tag false is Scott's left copy and the tag true is the right copy.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slotPre

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **Scott's tag-`i` tuple neighbourhood** `i ⋃_{j<n} 1ʲ0 X_j`: the union of the `n` slots, slot `j`
holding `X j` behind the prefix `i 1ʲ 0`. (For `i = false`/`true` these are Scott's left/right
copies, the `−`/`+` summands.) -/
def embTuple (i : Bool) (X : Fin n → Set Str) : Set Str :=
  {w | ∃ j : Fin n, ∃ w', w = slotPre i (j : ℕ) ++ w' ∧ w' ∈ X j}

end Example62A
end DomainTheory.NeighbourhoodSystems
