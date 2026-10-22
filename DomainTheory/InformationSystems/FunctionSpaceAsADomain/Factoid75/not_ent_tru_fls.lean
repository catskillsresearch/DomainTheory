module

public import Mathlib.Data.Multiset.MapFold
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

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem not_ent_tru_fls : ¬ boolSystem.Ent {BoolToken.tru} BoolToken.fls := by
  intro ⟨⟨p, hp⟩, hAll⟩
  have htru : boolSat p .tru := hp .tru (Finset.mem_singleton_self _)
  have hfls : boolSat p .fls := hAll p hp
  cases p <;> simp only [boolSat] at htru hfls

end InfoSys
end DomainTheory.InformationSystems
