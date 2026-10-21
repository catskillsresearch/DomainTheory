/-ai
The finset of right-pair payloads of a singleton left pair is empty.

A left pair contributes no right-pair payload, and the empty finset has no members.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_pairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

theorem pairRFinset_singleton_pairL (t : TreeToken α) :
    pairRFinset ({.pairL t} : Finset (TreeToken α)) = ∅ := by
  ext s
  constructor
  · intro hs
    exact False.elim (nomatch mem_pairRFinset.1 hs)
  · intro hs
    exact False.elim (Finset.notMem_empty s hs)

end InfoSys

end DomainTheory.InformationSystems
