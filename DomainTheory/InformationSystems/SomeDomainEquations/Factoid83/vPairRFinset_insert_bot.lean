/-ai
Inserting the bottom token into a finite set of tokens of V does not change its right projection.

Extensionality and the membership criterion for the right projection reduce the claim to membership in an inserted set. A right-pair token is never the bottom token, so a witness in the inserted set already lies in the original set, and a witness in the original set remains a witness after insertion.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairRFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

theorem vPairRFinset_insert_bot (u : Finset VToken) :
    vPairRFinset (insert (.bot : VToken) u) = vPairRFinset u := by
  ext t; simp only [mem_vPairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

end InfoSys

end DomainTheory.InformationSystems
