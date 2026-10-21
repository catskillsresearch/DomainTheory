/-ai
The tree product is the product information system of the tree system with itself.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Official product of the tree system with itself. -/
abbrev TreeProd : InfoSys (ProdToken (treeSystem A) (treeSystem A)) :=
  productSystem (treeSystem A) (treeSystem A)

end DomainTheory.BridgeTheorems
