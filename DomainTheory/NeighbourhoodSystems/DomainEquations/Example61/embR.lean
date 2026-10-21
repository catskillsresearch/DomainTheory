/-ai
The right tagging of a set of path-token pairs is the set of pairs whose path begins with the boolean false and whose remaining path, with the same token, lies in the original set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- `2Q = {(2::q, a) ∣ (q, a) ∈ Q}`: the `2`-prefixed copy of a `D^§`-neighbourhood `Q`. -/
def embR (Q : Set (List Bool × α)) : Set (List Bool × α) := {t | ∃ q', t.1 = false :: q' ∧ (q', t.2) ∈ Q}

end Example61
end DomainTheory.NeighbourhoodSystems
