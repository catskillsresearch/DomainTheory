module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

def EntSet (u v : Finset α) : Prop := ∀ X ∈ v, sys.Ent u X

end InfoSys

end DomainTheory.InformationSystems
