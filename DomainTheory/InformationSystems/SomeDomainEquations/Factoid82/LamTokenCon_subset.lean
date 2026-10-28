module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamCon_subset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamForgetFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem LamTokenCon_subset {u v : Finset (LamToken A)}
    (hu : LamTokenCon A u) (hv : v ⊆ u) : LamTokenCon A v :=
  LamCon_subset A hu (by
    intro t ht
    rcases (mem_lamForgetFinset A).1 ht with ⟨p, hp, rfl⟩
    exact (mem_lamForgetFinset A).2 ⟨p, hv hp, rfl⟩)

end InfoSys
end DomainTheory.InformationSystems
