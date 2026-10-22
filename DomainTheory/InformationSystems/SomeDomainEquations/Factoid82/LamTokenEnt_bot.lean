/-ai
A consistent finite set of lambda tokens entails the bottom lambda token.

The proof applies raw entailment of the bottom token to the consistency of the set.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEnt_bot

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem LamTokenEnt_bot {u : Finset (LamToken A)} (hu : LamTokenCon A u) :
    LamTokenEnt A u (lamBot A) :=
  LamEnt_bot A hu

end InfoSys
end DomainTheory.InformationSystems
