module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.botFinite
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.mem_finiteApproximants_of_le

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem nonempty_finiteApproximants (x : A.Element) :
    (finiteApproximants A x).Nonempty :=
  ⟨botFinite A, mem_finiteApproximants_of_le A (InfoSys.botElement.le A x)⟩

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
