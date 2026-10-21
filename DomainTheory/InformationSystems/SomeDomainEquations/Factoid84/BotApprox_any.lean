/-ai
Every approximable map from the powerset system P to itself satisfies Scott's bottom condition.

A token of the finite element of 0 equals 0. Membership of 0 in the image of the bottom element is witnessed by the empty set, which is contained in the bottom element because it has no members. The map relates the empty set to itself. The empty set entails itself, and it entails the singleton of 0 because the only token of that singleton is the bottom token. Monotonicity, whose consistency side conditions hold outright, turns that empty relation into the required relation.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_barElement

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem BotApprox_any (r : ApproximableMap P P) : BotApprox r := by
  intro x hx
  have hx0 : x = 0 := by
    rcases (mem_barElement 0 x).1 hx with rfl | rfl <;> rfl
  subst hx0
  refine ⟨∅, fun a ha => False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha)), ?_⟩
  have hempty := r.empty_rel
  have hbot : P.EntSet ∅ ({0} : Finset ℕ) := by
    intro z hz
    rw [Finset.mem_singleton] at hz; subst hz
    exact Or.inl rfl
  exact r.mono hempty (P.entSet_empty ∅) hbot trivial trivial

end Factoid84

end DomainTheory.InformationSystems
