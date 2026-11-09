module

public import DomainTheory.BridgeTheorems.interOf
import DomainTheory.BridgeTheorems.mem_interOf

@[expose] public section

namespace DomainTheory.BridgeTheorems



namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem interOf_subset_nbhd {u : Finset ι} {i : ι} (hi : i ∈ u) :
    B.interOf u ⊆ B.nbhd i := fun _ hx => (B.mem_interOf.mp hx).2 i hi

end NbhdBasis

end DomainTheory.BridgeTheorems
