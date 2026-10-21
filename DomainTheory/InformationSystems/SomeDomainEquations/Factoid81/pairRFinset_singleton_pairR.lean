/-ai
The finset of right-pair payloads of the singleton right pair of t is the singleton of t.

A token is such a payload exactly when the corresponding right pairs are equal, and right pairs are equal exactly when their payloads are equal.
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

theorem pairRFinset_singleton_pairR (t : TreeToken α) :
    pairRFinset ({.pairR t} : Finset (TreeToken α)) = {t} := by
  ext s; simp only [mem_pairRFinset, Finset.mem_singleton]
  exact ⟨fun h => TreeToken.pairR.inj h, fun h => congrArg TreeToken.pairR h⟩

end InfoSys

end DomainTheory.InformationSystems
