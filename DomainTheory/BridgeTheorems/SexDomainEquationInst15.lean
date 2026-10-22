/-ai
This instance records that insertion of a folded sum token commutes on the left. Inserting the folds of two sum tokens in either order gives the same finite set, by commutativity of insertion.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
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
