module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid26

inductive Token (A B : Type*) where
  | bot
  | pair (a : A) (b : B)
  deriving DecidableEq

end Factoid26
end DomainTheory.InformationSystems
