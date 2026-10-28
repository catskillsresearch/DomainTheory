module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDBot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_trans

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

def LamDEnt (u : Finset (LamDToken A)) (p : LamDToken A) : Prop :=
  LamEntDepth A (lamDForgetFinset A u) p.val

theorem LamDEnt.bot {u : Finset (LamDToken A)} (hu : LamDCon A u) :
    LamDEnt A u (lamDBot A) :=
  LamEntDepth.bot hu

theorem LamDEnt.of_mem {u : Finset (LamDToken A)} {p : LamDToken A}
    (hu : LamDCon A u) (hp : p ∈ u) : LamDEnt A u p :=
  LamEntDepth_of_mem A hu ((mem_lamDForgetFinset A).2 ⟨p, hp, rfl⟩)

theorem LamDEnt.trans {u v : Finset (LamDToken A)} {c : LamDToken A}
    (hv : LamDCon A v) (hu : LamDCon A u)
    (hEnts : ∀ t ∈ u, LamDEnt A v t) (ht : LamDEnt A u c) :
    LamDEnt A v c :=
  LamEntDepth_trans A hv hu
    (fun t ht' => by
      rcases (mem_lamDForgetFinset A).1 ht' with ⟨p, hp, rfl⟩
      exact hEnts p hp)
    ht

end InfoSys

end DomainTheory.InformationSystems
