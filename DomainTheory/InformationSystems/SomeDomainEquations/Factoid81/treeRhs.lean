module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeSystem

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

/-- The right-hand side of the domain equation is the official sum of products. -/
def treeRhs : InfoSys (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  sumSystem A (productSystem (treeSystem A) (treeSystem A))

theorem treeRhs.eq_sum_product :
    treeRhs A = sumSystem A (productSystem (treeSystem A) (treeSystem A)) :=
  rfl

end InfoSys


end DomainTheory.InformationSystems
