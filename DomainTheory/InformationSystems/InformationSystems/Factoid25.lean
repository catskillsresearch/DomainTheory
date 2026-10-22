module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys

public import DomainTheory.InformationSystems.InformationSystems.Factoid25.Token
public import DomainTheory.InformationSystems.InformationSystems.Sat
public import DomainTheory.InformationSystems.InformationSystems.ofSatisfaction
public import DomainTheory.InformationSystems.InformationSystems.instDecidableEq
public import DomainTheory.InformationSystems.InformationSystems.sat_midpoint
public import DomainTheory.InformationSystems.InformationSystems.sat_sing

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid25

namespace Token


end Token


/-- **Factoid 2.5.** Interval information system of Scott 1982, §2. -/
def example_25 : InfoSys Token :=
  ofSatisfaction Sat Token.bot (fun _ => trivial) sat_sing

end Factoid25

end DomainTheory.InformationSystems
