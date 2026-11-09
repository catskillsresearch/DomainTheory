module

public import DomainTheory.BridgeTheorems.interOf
import DomainTheory.BridgeTheorems.mem_interOf

@[expose] public section

namespace DomainTheory.BridgeTheorems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem interOf_anti {u v : Finset ι} (h : u ⊆ v) : B.interOf v ⊆ B.interOf u := by
  intro x hx
  exact B.mem_interOf.mpr ⟨(B.mem_interOf.mp hx).1, fun i hi => (B.mem_interOf.mp hx).2 i (h hi)⟩

end NbhdBasis

end DomainTheory.BridgeTheorems
