module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- `0X = {([], a) ∣ a ∈ X}`: the `0`-tagged copy of a `D`-neighbourhood `X` (empty `{1,2}`-path). -/
def embZero (X : Set α) : Set (List Bool × α) := {t | t.1 = [] ∧ t.2 ∈ X}

end Example61
end DomainTheory.NeighbourhoodSystems
