/-ai
A consistent finite set of raw lambda tokens entails the bottom token.

Consistency is consistency at some stage. At stage zero, stage-zero entailment of bottom is that consistency. At a successor stage, the successor consistency is the new disjunct of successor entailment of bottom.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
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
