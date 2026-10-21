/-ai
A neighbourhood of Example 1.2 that contains the master is the master.

By the classification of neighbourhoods it is the master, {0}, or {1}. The last two alternatives would contain the master in {0} or in {1}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_iff
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master_not_subset_zero
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master_not_subset_one

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example12

theorem eq_of_master_subset {Y : Set Token} (h : mem Y) (hsub : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp h with rfl | hzero | hone
  · rfl
  · exact absurd hzero (fun h' => master_not_subset_zero (h' ▸ hsub))
  · exact absurd hone (fun h' => master_not_subset_one (h' ▸ hsub))

end DomainTheory.NeighbourhoodSystems.Example12
