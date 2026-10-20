module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UCon_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UCon_subset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UCon_insert_of_ent
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UEnt_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UEnt_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UEnt_trans

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- **Scott (7)–(10).** The universal-domain information system `U`. -/
def uSystem : InfoSys UToken where
  bot := uBot
  Con := {u | UCon u}
  Ent := UEnt
  con_subset := fun hu hv => UCon_subset hu hv
  con_sing := UCon_singleton
  ent_con := fun h => UCon_insert_of_ent h
  ent_bot := fun hu => UEnt_bot hu
  ent_refl := fun hu hp => UEnt_of_mem hu hp
  ent_trans := fun hv hu hEnts h => UEnt_trans hv hu hEnts h

end InfoSys

end DomainTheory.InformationSystems
