module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_fixed

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

theorem proposition_7_4_ii (f : ApproximableMap A A) :
    f.toElement (fixElement A f) = fixElement A f :=
  fixElement_fixed A f

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
