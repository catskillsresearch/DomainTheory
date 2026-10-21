/-ai
Scott's information system V takes every finite set of tokens to be consistent. Its bottom token is the bottom of V, its consistency predicate is VCon, and its entailment is VEnt. The consistency obligations hold outright. The bottom token is entailed, a member of a finite set is entailed by that set, and entailment is transitive.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_trans

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- **Scott (1)–(6).** The information system `V` (all finite sets consistent). -/
def vSystem : InfoSys VToken where
  bot := vBot
  Con := {u | VCon u}
  Ent := VEnt
  con_subset := fun _ _ => trivial
  con_sing := fun _ => trivial
  ent_con := fun _ => trivial
  ent_bot := fun _ => VEnt.bot
  ent_refl := fun _ hp => VEnt_of_mem hp
  ent_trans := fun _ _ hEnts h => VEnt_trans hEnts h

end InfoSys

end DomainTheory.InformationSystems
