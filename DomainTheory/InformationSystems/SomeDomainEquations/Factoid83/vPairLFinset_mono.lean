/-ai
The left projection of finite sets of tokens of V is monotone.

A token of the left projection of the smaller set has its left-pair token in that set, hence in the larger set, and therefore lies in the left projection of the larger set.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairLFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem vPairLFinset_mono {u v : Finset VToken} (h : u ⊆ v) :
    vPairLFinset u ⊆ vPairLFinset v := by
  intro t ht
  exact mem_vPairLFinset.2 (h (mem_vPairLFinset.1 ht))

end InfoSys

end DomainTheory.InformationSystems
