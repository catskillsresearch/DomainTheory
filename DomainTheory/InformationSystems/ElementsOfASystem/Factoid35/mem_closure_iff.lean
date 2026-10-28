
module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.closure

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem mem_closure_iff {u : Finset α} (hu : u ∈ sys.Con) {X : α} :
    X ∈ (sys.closure u hu).carrier ↔ sys.Ent u X := Iff.rfl

end InfoSys
end DomainTheory.InformationSystems
