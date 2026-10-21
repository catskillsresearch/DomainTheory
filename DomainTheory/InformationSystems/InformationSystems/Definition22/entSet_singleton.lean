/-ai
A finite set u set-entails the singleton of a token X if and only if u entails X.

From set-entailment of the singleton, the token X belongs to its own singleton, so u entails X. Conversely, any member of the singleton equals X, and substituting that equality turns the entailment of X into set-entailment of the singleton.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Definition22.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)


theorem entSet_singleton {u : Finset α} {X : α} :
    sys.EntSet u {X} ↔ sys.Ent u X := by
  constructor
  · intro h
    exact h X (Finset.mem_singleton_self X)
  · intro h Y hY
    rw [Finset.mem_singleton] at hY
    subst hY
    exact h

end InfoSys
end DomainTheory.InformationSystems
