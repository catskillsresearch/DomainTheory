/-ai
The identity map of the powerset system P fails Scott's rogue condition.

If the image of the finite element of 1 were the top element, the token 2 would belong to that image. Some finite set contained in the finite element of 1 would then entail the singleton of 2 through the identity relation. The token 2 does not equal 0, so it would belong to that finite set and hence to the finite element of 1, whose members are 0 or 1.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84


































theorem not_RogueApprox_idMap : ¬ RogueApprox (idMap P) := by
  intro h
  have h2 : 2 ∈ ((idMap P).toElement (barElement 1)).carrier := by
    rw [h]; exact mem_topElement 2
  rcases (mem_toElement (idMap P) (barElement 1)).1 h2 with ⟨u, hu, hrel⟩
  have hEnt : P.EntSet u {2} := hrel.2.2
  have h2u := hEnt 2 (Finset.mem_singleton_self 2)
  rcases h2u with h0 | h2u
  · exact absurd h0 (by decide)
  · have : 2 ∈ (barElement 1).carrier := hu (Finset.mem_coe.2 h2u)
    rcases (mem_barElement 1 2).1 this with h0 | h1'
    · exact absurd h0 (by decide)
    · exact absurd h1' (by decide)

end Factoid84
end DomainTheory.InformationSystems
