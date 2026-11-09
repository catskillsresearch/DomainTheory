module

public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
import DomainTheory.BridgeTheorems.interOf_empty
import DomainTheory.BridgeTheorems.interOf_insert

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems


namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem filter_mem_interOf (x : B.system.Element) {u : Finset ι}
    (hu : ∀ i ∈ u, x.mem (B.nbhd i)) : x.mem (B.interOf u) := by
  induction u using Finset.induction with
  | empty =>
    simpa [interOf_empty] using x.master_mem
  | insert a s ha ih =>
    rw [B.interOf_insert ha]
    exact x.inter_mem (hu a (Finset.mem_insert_self a s))
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

end NbhdBasis

end DomainTheory.BridgeTheorems
