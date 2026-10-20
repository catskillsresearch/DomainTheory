module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_insert_of_ent
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt_trans
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_subset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- **Factoid 8.1.** Tree information system solving `T ≅ A + (T × T)` by construction. -/
def treeSystem : InfoSys (TreeToken α) where
  bot := treeBot
  Con := {u | TreeCon A u}
  Ent := TreeEnt A
  con_subset := fun hu hv => TreeCon_subset A hu hv
  con_sing := TreeCon_singleton A
  ent_con := fun h => TreeCon_insert_of_ent A h
  ent_bot := fun hu => ⟨hu, trivial⟩
  ent_refl := fun hu hp => TreeEnt_of_mem A hu hp
  ent_trans := fun hv hu hEnts hEntc => TreeEnt_trans A hv hu hEnts hEntc

end InfoSys

end DomainTheory.InformationSystems
