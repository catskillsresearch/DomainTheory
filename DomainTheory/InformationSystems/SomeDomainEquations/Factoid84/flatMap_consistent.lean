/-ai
The flat map satisfies Scott's consistency condition: the finite element of 1 is not contained in the image of the finite element of 0.

The token 1 belongs to the finite element of 1. If it belonged to that image, some finite set contained in the finite element of 0 would be flat-related to the singleton of 1. If 1 belonged to that finite set, it would belong to the finite element of 0, whose members equal 0. The other clause of the flat relation excludes 1 from the singleton of 1.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_barElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatMap_consistent : ConsistentApprox flatMap := by
  intro hsub
  have h1 : 1 ∈ (barElement 1).carrier := (mem_barElement 1 1).2 (Or.inr rfl)
  have h1' : 1 ∈ (flatMap.toElement (barElement 0)).carrier := hsub h1
  rcases (mem_toElement flatMap (barElement 0)).1 h1' with ⟨u, hu, hrel⟩
  rcases hrel with h1u | ⟨_, hv1⟩
  · have : 1 ∈ (barElement 0).carrier := hu (Finset.mem_coe.2 h1u)
    rcases (mem_barElement 0 1).1 this with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact hv1 (Finset.mem_singleton_self 1)

end Factoid84

end DomainTheory.InformationSystems
