module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

inductive SumToken (α β : Type*) where
  | left : α → SumToken α β
  | right : β → SumToken α β
  | bot : SumToken α β

end InfoSys
end DomainTheory.InformationSystems
