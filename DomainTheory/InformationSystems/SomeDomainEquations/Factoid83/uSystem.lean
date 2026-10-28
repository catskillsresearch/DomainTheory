module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UCon_insert_of_ent

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

def uSystem : InfoSys UToken where
  bot := uBot
  Con := {u | UCon u}
  Ent := UEnt
  con_subset := fun hu hv => UCon.subset hu hv
  con_sing := UCon.singleton
  ent_con := fun h => UCon_insert_of_ent h
  ent_bot := fun hu => UEnt.bot hu
  ent_refl := fun hu hp => UEnt.of_mem hu hp
  ent_trans := fun hv hu hEnts h => UEnt.trans hv hu hEnts h

end InfoSys

end DomainTheory.InformationSystems
