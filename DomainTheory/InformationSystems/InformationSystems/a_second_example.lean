module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys

public import DomainTheory.InformationSystems.InformationSystems.Token
public import DomainTheory.InformationSystems.InformationSystems.Sat

@[expose] public section

namespace DomainTheory.InformationSystems

def a_second_example : InfoSys Token :=
  ofSatisfaction Sat Token.bot (fun _ => trivial) sat_sing

end DomainTheory.InformationSystems
