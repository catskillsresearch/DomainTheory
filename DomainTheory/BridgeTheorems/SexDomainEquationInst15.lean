module

public import DomainTheory.BridgeTheorems.foldInsert

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

instance : LeftCommutative (foldInsert (A := A)) :=
  ⟨fun p q t => insert_comm' (treeFold A p) (treeFold A q) t⟩

end DomainTheory.BridgeTheorems
