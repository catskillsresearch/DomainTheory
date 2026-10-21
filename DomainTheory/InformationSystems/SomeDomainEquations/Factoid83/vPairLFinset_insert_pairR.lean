/-ai
Inserting a right-pair token into a finite set of tokens of V does not change its left projection.

Extensionality and the membership criterion for the left projection reduce the claim to membership in an inserted set. A left-pair token is never a right-pair token, so a witness in the inserted set already lies in the original set, and a witness in the original set remains a witness after insertion.
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

theorem vPairLFinset_insert_pairR (u : Finset VToken) (t : VToken) :
    vPairLFinset (insert (.pairR t) u) = vPairLFinset u := by
  ext s; simp only [mem_vPairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

end InfoSys

end DomainTheory.InformationSystems
