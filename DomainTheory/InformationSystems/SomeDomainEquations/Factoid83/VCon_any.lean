/-ai
Every finite set of V-tokens is consistent.

The proof is the trivial inhabitant of truth.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false



























theorem VCon_any (u : Finset VToken) : VCon u := trivial

end InfoSys
end DomainTheory.InformationSystems
