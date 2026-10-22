module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.EmptyEntails

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem emptyEntails_funion {γ : Type*} [DecidableEq γ] (sys : InfoSys γ)
    {u v : Finset γ} :
    EmptyEntails sys (u ∪' v) ↔ EmptyEntails sys u ∧ EmptyEntails sys v := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (subset_funion_left _ _ hx),
      fun x hx => h x (subset_funion_right _ _ hx)⟩
  · intro ⟨hu, hv⟩ x hx
    rcases mem_funion.mp hx with hx | hx
    · exact hu x hx
    · exact hv x hx

end InfoSys

end DomainTheory.InformationSystems
