/-ai
A neighbourhood of Example 1.3 that contains the master is the master.

By the classification of neighbourhoods it is the master, {1, 2}, or {2}. The last two alternatives would contain the master in {1, 2} or in {2}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_iff
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master_not_subset_twelve
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master_not_subset_two

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example13

theorem eq_of_master_subset {Y : Set Token} (h : mem Y) (hsub : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp h with rfl | htwelve | htwo
  · rfl
  · exact absurd htwelve (fun h' => master_not_subset_twelve (h' ▸ hsub))
  · exact absurd htwo (fun h' => master_not_subset_two (h' ▸ hsub))

end DomainTheory.NeighbourhoodSystems.Example13
