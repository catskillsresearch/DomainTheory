/-ai
The finset of right-pair payloads is monotone: if v is contained in u, then every right-pair payload of v is a right-pair payload of u.

A payload of v comes from a right pair that belongs to v, and that right pair still belongs to u.
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

theorem pairRFinset_mono {u v : Finset (TreeToken α)} (h : v ⊆ u) :
    pairRFinset v ⊆ pairRFinset u := fun _ ht => mem_pairRFinset.2 (h (mem_pairRFinset.1 ht))

end InfoSys

end DomainTheory.InformationSystems
