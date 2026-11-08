module

public import DomainTheory.InformationSystems.InformationSystems.partialFunctionSystem

@[expose] public section

namespace DomainTheory.InformationSystems

def a_third_example (A B : Type*) [DecidableEq A] [DecidableEq B] :
    InfoSys (PartialFunToken A B) :=
  partialFunctionSystem A B

end DomainTheory.InformationSystems
