module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem vPairRFinset_mono {u v : Finset VToken} (h : u ⊆ v) :
    vPairRFinset u ⊆ vPairRFinset v := by
  intro t ht
  exact mem_vPairRFinset.2 (h (mem_vPairRFinset.1 ht))

end InfoSys

end DomainTheory.InformationSystems
