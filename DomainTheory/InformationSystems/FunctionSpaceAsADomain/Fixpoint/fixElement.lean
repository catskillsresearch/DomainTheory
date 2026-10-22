
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

namespace ApproximableMap

/-- Least fixed point of an approximable endomap, as an element. -/
def fixElement (f : ApproximableMap A A) : A.Element :=
  (fixMap A).toElement (approxMap_toElement A A f)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
