/-ai
The left pair projection is monotone with respect to inclusion of finite sets of tree tokens.

A token of the smaller projection is a left-pair token of the smaller set, hence of the larger set by the inclusion, and therefore a token of the larger projection.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_pairLFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

theorem pairLFinset_mono {u v : Finset (TreeToken α)} (h : v ⊆ u) :
    pairLFinset v ⊆ pairLFinset u := fun _ ht => mem_pairLFinset.2 (h (mem_pairLFinset.1 ht))

end InfoSys

end DomainTheory.InformationSystems
