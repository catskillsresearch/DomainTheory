module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem treeUnfold_pairR (t : TreeToken α) :
    treeUnfold A (.pairR t) = .right ⟨(treeBot, t), ⟨Or.inl rfl⟩⟩ := rfl

end InfoSys
end DomainTheory.InformationSystems
