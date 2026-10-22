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

theorem vPairLFinset_insert_bot (u : Finset VToken) :
    vPairLFinset (insert (.bot : VToken) u) = vPairLFinset u := by
  ext t; simp only [mem_vPairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

end InfoSys

end DomainTheory.InformationSystems
