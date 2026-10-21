/-ai
A token lies in the closure of a consistent finite set if and only if that set entails the token.

The equivalence is the definition of the closure.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem mem_closure_iff {u : Finset α} (hu : u ∈ sys.Con) {X : α} :
    X ∈ (sys.closure u hu).carrier ↔ sys.Ent u X := Iff.rfl

end InfoSys
end DomainTheory.InformationSystems
