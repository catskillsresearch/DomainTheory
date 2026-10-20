module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Consistent
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.consistent_singleton
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.consistent_subset
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.consistent_insert_bot
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.consistent_insert_mem
public import DomainTheory.InformationSystems.InformationSystems.Factoid26.Ent

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid26

/-- **Factoid 2.6.** Partial-function information system of Scott 1982, §2. -/
def partialFunctionSystem (A B : Type*) [DecidableEq A] [DecidableEq B] :
    InfoSys (Token A B) where
  bot := Token.bot
  Con := {u | Consistent u}
  Ent := Ent
  con_subset := by
    intro u v hu hv
    exact consistent_subset hv hu
  con_sing := fun t => consistent_singleton t
  ent_con := by
    rintro u a ⟨hu, hX⟩
    rcases hX with rfl | hmem
    · exact consistent_insert_bot hu
    · exact consistent_insert_mem hmem hu
  ent_bot := by
    intro u hu
    exact ⟨hu, Or.inl rfl⟩
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, Or.inr ha⟩
  ent_trans := by
    intro u v c hv _hu hvu ⟨_, hc⟩
    refine ⟨hv, ?_⟩
    rcases hc with rfl | hc
    · exact Or.inl rfl
    · have ⟨_, hcv⟩ := hvu c hc
      exact hcv

end Factoid26

end DomainTheory.InformationSystems
