module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VCon

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

def vSystem : InfoSys VToken where
  bot := vBot
  Con := {u | VCon u}
  Ent := VEnt
  con_subset := fun _ _ => trivial
  con_sing := fun _ => trivial
  ent_con := fun _ => trivial
  ent_bot := fun _ => VEnt.bot
  ent_refl := fun _ hp => VEnt.of_mem hp
  ent_trans := fun _ _ hEnts h => VEnt.trans hEnts h

end InfoSys

end DomainTheory.InformationSystems
