module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon_subset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDEnt_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDEnt_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon_insert_of_ent
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDEnt_trans

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- **Definition 2.1 packaging.** The λ-calculus information system `D`. -/
def lambdaSystem : InfoSys (LamDToken A) where
  bot := lamDBot A
  Con := {u | LamDCon A u}
  Ent := LamDEnt A
  con_subset := fun hu hv => LamDCon_subset A hu hv
  con_sing := LamDCon_singleton A
  ent_con := fun h => LamDCon_insert_of_ent A h
  ent_bot := fun hu => LamDEnt_bot A hu
  ent_refl := fun hu hp => LamDEnt_of_mem A hu hp
  ent_trans := fun hv hu hEnts hEntc => LamDEnt_trans A hv hu hEnts hEntc

end InfoSys

end DomainTheory.InformationSystems
