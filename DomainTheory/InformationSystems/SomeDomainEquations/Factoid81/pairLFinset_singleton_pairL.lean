/-ai
The left pair projection of the singleton consisting of a left-pair token is the singleton of its inner token.

Membership in the projection is membership of the left-pair token in the singleton. The left-pair constructor is injective, and an equality of inner tokens is preserved by the left-pair constructor.
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

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

theorem pairLFinset_singleton_pairL (t : TreeToken α) :
    pairLFinset ({.pairL t} : Finset (TreeToken α)) = {t} := by
  ext s; simp only [mem_pairLFinset, Finset.mem_singleton]
  exact ⟨fun h => TreeToken.pairL.inj h, fun h => congrArg TreeToken.pairL h⟩

end InfoSys

end DomainTheory.InformationSystems
