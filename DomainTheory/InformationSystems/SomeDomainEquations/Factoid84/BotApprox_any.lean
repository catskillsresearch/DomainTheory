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
