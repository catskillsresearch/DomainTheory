/-ai
If a consistent Boolean set entails the false token, then the singleton false token entails every token of that set.

The entailment of false supplies a Boolean point that holds of the set and satisfies false. The undefined and true points do not satisfy false. The false point holds of the token in question, so that token is bottom or false, and in each of those cases the singleton false token entails it by a false-point witness. The token cannot be true.
ai-/
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

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem entSet_singleton_fls_of_ent_fls {u : Finset BoolToken}
    (_hu : u ∈ boolSystem.Con) (h : boolSystem.Ent u .fls) :
    boolSystem.EntSet ({BoolToken.fls} : Finset BoolToken) u := by
  intro t ht
  obtain ⟨⟨p, hp⟩, hAll⟩ := h
  have hfls : boolSat p .fls := hAll p hp
  cases p with
  | undef => simp only [boolSat] at hfls
  | isTrue => simp only [boolSat] at hfls
  | isFalse =>
    have hsat : boolSat .isFalse t := hp t ht
    cases t with
    | bot =>
      exact ⟨⟨.isFalse, fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun _ _ => boolSat_bot _⟩
    | fls =>
      exact ⟨⟨.isFalse, fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun q hq => hq .fls (Finset.mem_singleton_self _)⟩
    | tru => exact False.elim hsat

end InfoSys
end DomainTheory.InformationSystems
