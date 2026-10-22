module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem vPairLFinset_insert_top (u : Finset VToken) :
    vPairLFinset (insert (.top : VToken) u) = vPairLFinset u := by
  ext t; simp only [mem_vPairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

end InfoSys
end DomainTheory.InformationSystems
