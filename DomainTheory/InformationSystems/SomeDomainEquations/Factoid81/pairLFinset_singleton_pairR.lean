/-ai
The left pair projection of the singleton consisting of a right-pair token is empty.

A left-pair token in that projection would belong to the singleton and hence be a right-pair token, which is impossible, and the empty set has no members.
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

theorem pairLFinset_singleton_pairR (t : TreeToken α) :
    pairLFinset ({.pairR t} : Finset (TreeToken α)) = ∅ := by
  ext s
  constructor
  · intro hs
    exact False.elim (nomatch mem_pairLFinset.1 hs)
  · intro hs
    exact False.elim (Finset.notMem_empty s hs)

end InfoSys

end DomainTheory.InformationSystems
