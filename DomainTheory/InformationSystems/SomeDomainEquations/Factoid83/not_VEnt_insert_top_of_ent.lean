module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_insert_top_imp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- Adding an entailed non-top token cannot create a top-entailment. -/
theorem not_VEnt_insert_top_of_ent {u : Finset VToken} {y : VToken}
    (hy : y ≠ .top) (hEnt : VEnt u y) (hNot : ¬ VEnt u .top) :
    ¬ VEnt (insert y u) .top :=
  fun hIns => hNot (VEnt_insert_top_imp hy hEnt hIns)

end InfoSys

end DomainTheory.InformationSystems
