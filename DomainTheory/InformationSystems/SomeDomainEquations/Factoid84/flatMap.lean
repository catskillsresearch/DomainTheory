module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatRel
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatRel_empty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

def flatMap : ApproximableMap P P where
  rel := flatRel
  rel_dom := fun _ => trivial
  rel_cod := fun _ => trivial
  empty_rel := flatRel_empty
  union_right := by
    intro u v v' hv hv'
    rcases hv with h1 | ⟨hv, hv1⟩
    · exact Or.inl h1
    · rcases hv' with h1 | ⟨hv', hv1'⟩
      · exact Or.inl h1
      · refine Or.inr ⟨?_, ?_⟩
        · intro n hn
          rcases mem_funion.1 hn with h | h
          · exact hv n h
          · exact hv' n h
        · intro h1
          rcases mem_funion.1 h1 with h | h
          · exact hv1 h
          · exact hv1' h
  mono := by
    intro u u' v v' hrel hEntu hEntv _ _
    rcases hrel with h1 | ⟨hv, hv1⟩
    · -- 1 ∈ u; show 1 ∈ u' from EntSet
      have h := hEntu 1 h1
      rcases h with h0 | h1'
      · exact False.elim (by cases h0)
      · exact Or.inl h1'
    · refine Or.inr ⟨?_, ?_⟩
      · intro n hn
        have hn' := hEntv n hn
        rcases hn' with rfl | hn'
        · exact Or.inl rfl
        · have hn'' := hv n hn'
          rcases hn'' with rfl | hn''
          · exact Or.inl rfl
          · have hu' := hEntu n hn''
            rcases hu' with rfl | hu'
            · exact Or.inl rfl
            · exact Or.inr hu'
      · intro h1v
        have h := hEntv 1 h1v
        rcases h with h0 | h1v'
        · exact False.elim (by cases h0)
        · exact hv1 h1v'

end Factoid84

end DomainTheory.InformationSystems
