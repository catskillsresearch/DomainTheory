
module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.theorem_7_2
public import DomainTheory.InformationSystems.InformationSystems.a_second_example
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.StrictToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def StrictFunToken : Type _ :=
  {p : FunToken A B // StrictToken A B p}

end InfoSys

end DomainTheory.InformationSystems
