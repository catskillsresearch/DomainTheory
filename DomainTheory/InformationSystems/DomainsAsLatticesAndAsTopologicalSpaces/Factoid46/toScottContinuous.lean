
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.ScottContinuous
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.toElement_directedSup

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

/-- **Factoid 4.6 (→).** Every approximable map is Scott-continuous on elements. -/
def toScottContinuous (f : ApproximableMap A B) : ScottContinuous A B where
  toFun := f.toElement
  mono' := f.toElement_mono
  map_directedSup := f.toElement_directedSup

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
