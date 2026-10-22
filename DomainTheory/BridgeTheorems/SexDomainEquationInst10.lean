/-ai
This instance records that insertion of an unfolded tree token commutes on the left. Inserting the unfoldings of two tokens in either order gives the same finite set, by commutativity of insertion.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.unfoldInsert

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

instance : LeftCommutative (unfoldInsert (A := A)) :=
  ⟨fun p q s => insert_comm' (treeUnfold A p) (treeUnfold A q) s⟩

end DomainTheory.BridgeTheorems
