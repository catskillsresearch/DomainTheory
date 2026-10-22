module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem LamEnt_bot {u : Finset (RawLamToken α)} (hu : LamCon A u) :
    LamEnt A u .bot := by
  rcases hu with ⟨n, hu⟩
  cases n with
  | zero => exact ⟨0, hu⟩
  | succ n => exact ⟨n + 1, Or.inr hu⟩

end InfoSys
end DomainTheory.InformationSystems
