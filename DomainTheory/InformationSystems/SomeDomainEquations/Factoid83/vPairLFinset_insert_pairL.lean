/-ai
The left projection of a finite set with a left-pair token of payload t inserted is the left projection of the original set with t inserted.

Extensionality and the membership criterion turn both sides into membership of a left-pair token in an inserted set. If the inserted token is the left-pair of the candidate, injectivity of the left-pair constructor gives equality of payloads; otherwise the witness already lies in the original set. Conversely, an equal payload or a witness in the original projection supplies the matching disjunct.
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

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

theorem vPairLFinset_insert_pairL (u : Finset VToken) (t : VToken) :
    vPairLFinset (insert (.pairL t) u) = insert t (vPairLFinset u) := by
  ext s; simp only [Finset.mem_insert, mem_vPairLFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (VToken.pairL.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

end InfoSys

end DomainTheory.InformationSystems
