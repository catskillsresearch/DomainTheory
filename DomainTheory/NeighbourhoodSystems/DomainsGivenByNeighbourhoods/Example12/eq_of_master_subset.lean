module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master_not_subset_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master_not_subset_one

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example12

theorem eq_of_master_subset {Y : Set Token} (h : mem Y) (hsub : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp h with rfl | hzero | hone
  · rfl
  · exact absurd hzero (fun h' => master_not_subset_zero (h' ▸ hsub))
  · exact absurd hone (fun h' => master_not_subset_one (h' ▸ hsub))

end DomainTheory.NeighbourhoodSystems.Example12
