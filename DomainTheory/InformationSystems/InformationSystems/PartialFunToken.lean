module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

inductive PartialFunToken (A B : Type*) where
  | bot
  | pair (a : A) (b : B)
  deriving DecidableEq

end DomainTheory.InformationSystems
