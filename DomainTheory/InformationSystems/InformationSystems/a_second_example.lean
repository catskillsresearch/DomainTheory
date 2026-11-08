module

public import DomainTheory.InformationSystems.InformationSystems.Sat

@[expose] public section

namespace DomainTheory.InformationSystems

def a_second_example : InfoSys Token :=
  ofSatisfaction Sat Token.bot (fun _ => trivial) sat_sing

end DomainTheory.InformationSystems
