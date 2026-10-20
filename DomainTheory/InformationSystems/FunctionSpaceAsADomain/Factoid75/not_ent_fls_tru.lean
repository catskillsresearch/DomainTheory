module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)


























open ApproximableMap












theorem not_ent_fls_tru : ¬ boolSystem.Ent {BoolToken.fls} BoolToken.tru := by
  intro ⟨⟨p, hp⟩, hAll⟩
  have hfls : boolSat p .fls := hp .fls (Finset.mem_singleton_self _)
  have htru : boolSat p .tru := hAll p hp
  cases p <;> simp only [boolSat] at htru hfls

end InfoSys
end DomainTheory.InformationSystems
