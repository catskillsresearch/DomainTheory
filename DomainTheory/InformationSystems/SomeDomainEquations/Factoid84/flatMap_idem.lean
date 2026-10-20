module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatMap_idem : IdemApprox flatMap := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · rintro ⟨w, hf, hg⟩
    rcases hf with h1u | ⟨hw, hw1⟩
    · exact Or.inl h1u
    · rcases hg with h1w | ⟨hv, hv1⟩
      · exact False.elim (hw1 h1w)
      · refine Or.inr ⟨?_, hv1⟩
        · intro n hn
          have hn' := hv n hn
          rcases hn' with rfl | hn'
          · exact Or.inl rfl
          · exact hw n hn'
  · intro h
    rcases h with h1u | ⟨hv, hv1⟩
    · exact ⟨insert 1 v, Or.inl h1u, Or.inl (Finset.mem_insert_self 1 v)⟩
    · exact ⟨v, Or.inr ⟨hv, hv1⟩, Or.inr ⟨fun n hn => Or.inr hn, hv1⟩⟩

end Factoid84

end DomainTheory.InformationSystems
