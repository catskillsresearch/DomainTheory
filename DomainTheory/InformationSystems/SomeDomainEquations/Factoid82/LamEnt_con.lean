/-ai
If a finite set of raw lambda tokens entails a raw token, then the set is consistent.

An entailment is entailment at some stage, and stage entailment yields stage consistency, which is consistency.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntN_con

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem LamEnt_con {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : LamEnt A u t) : LamCon A u := by
  rcases ht with ⟨n, ht⟩
  exact ⟨n, LamEntN_con A ht⟩

end InfoSys
end DomainTheory.InformationSystems
