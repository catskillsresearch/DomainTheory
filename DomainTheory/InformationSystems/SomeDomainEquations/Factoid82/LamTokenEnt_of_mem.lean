module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEnt_of_mem

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem LamTokenEnt_of_mem {u : Finset (LamToken A)} {p : LamToken A}
    (hu : LamTokenCon A u) (hp : p ∈ u) : LamTokenEnt A u p :=
  LamEnt_of_mem A hu ((mem_lamForgetFinset A).2 ⟨p, hp, rfl⟩)

end InfoSys
end DomainTheory.InformationSystems
