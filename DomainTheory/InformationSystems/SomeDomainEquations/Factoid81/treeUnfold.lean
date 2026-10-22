module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeSystem

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Unfold a tree token into the sum-of-product carrier. -/
def treeUnfold (t : TreeToken α) :
    SumToken α (ProdToken (treeSystem A) (treeSystem A)) :=
  match t with
  | .bot => .bot
  | .atom x => .left x
  | .pairL t => .right ⟨(t, treeBot), ⟨Or.inr rfl⟩⟩
  | .pairR t => .right ⟨(treeBot, t), ⟨Or.inl rfl⟩⟩

end InfoSys

end DomainTheory.InformationSystems
