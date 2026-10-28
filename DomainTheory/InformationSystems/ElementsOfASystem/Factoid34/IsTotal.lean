
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def IsTotal (x : sys.Element) : Prop := ∀ y, x ≤ y → y ≤ x

end InfoSys

end DomainTheory.InformationSystems
