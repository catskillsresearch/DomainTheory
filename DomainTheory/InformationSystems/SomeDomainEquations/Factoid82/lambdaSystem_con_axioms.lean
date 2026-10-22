module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamTokenCon_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamTokenCon_subset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamTokenEnt_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamTokenEnt_of_mem

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


/-- Def 2.1 progress: `con_subset`, `con_sing`, `ent_bot`, `ent_refl`;
`ent_con` for bot/atom; `ent_con`/`ent_trans` on `funTok` remain. -/
theorem lambdaSystem_con_axioms :
    (∀ {u v : Finset (LamToken A)}, LamTokenCon A u → v ⊆ u → LamTokenCon A v) ∧
      (∀ p : LamToken A, LamTokenCon A {p}) ∧
        (∀ {u : Finset (LamToken A)}, LamTokenCon A u → LamTokenEnt A u (lamBot A)) ∧
          (∀ {u : Finset (LamToken A)} {p : LamToken A},
            LamTokenCon A u → p ∈ u → LamTokenEnt A u p) :=
  ⟨fun hu hv => LamTokenCon_subset A hu hv,
    LamTokenCon_singleton A,
    fun hu => LamTokenEnt_bot A hu,
    fun hu hp => LamTokenEnt_of_mem A hu hp⟩


end InfoSys
end DomainTheory.InformationSystems
