
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def AllConsistent : Prop := ∀ u : Finset α, u ∈ sys.Con

end InfoSys

end DomainTheory.InformationSystems
