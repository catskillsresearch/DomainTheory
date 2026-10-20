module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable {A : InfoSys α} {B : InfoSys β}

def Le (f g : ApproximableMap A B) : Prop := ∀ ⦃u v⦄, f.rel u v → g.rel u v

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
