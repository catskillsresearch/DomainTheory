/-ai
Unfolding the tree bottom is the bottom token of the sum.

The two sides are definitionally the same.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u




variable {α : Type*} [DecidableEq α]















































variable (A : InfoSys α)

























theorem treeUnfold_bot : treeUnfold A treeBot = SumToken.bot := rfl

end InfoSys
end DomainTheory.InformationSystems
