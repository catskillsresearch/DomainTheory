/-ai
The neighbourhood {1, 2} is the set obtained by inserting the token 2 into the singleton {1}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example13

/-- The neighbourhood `{1, 2}`. -/
def twelve : Set Token := (insert 2 {1} : Set Token)

end DomainTheory.NeighbourhoodSystems.Example13
