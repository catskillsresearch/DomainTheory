module

public import DomainTheory.InformationSystems.SomeDomainEquations.treeSystem

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

abbrev TreeProd : InfoSys (ProdToken (treeSystem A) (treeSystem A)) :=
  productSystem (treeSystem A) (treeSystem A)

end DomainTheory.BridgeTheorems
