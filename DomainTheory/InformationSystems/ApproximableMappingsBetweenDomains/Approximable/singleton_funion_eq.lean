module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ext

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

theorem singleton_funion_eq (a : β) (s : Finset β) :
    ({a} : Finset β) ∪' s = insert a s := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with ha | hs
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp ha))
    · exact Finset.mem_insert_of_mem hs
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | hs
    · exact mem_funion.mpr (Or.inl (Finset.mem_singleton.mpr ha))
    · exact mem_funion.mpr (Or.inr hs)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
