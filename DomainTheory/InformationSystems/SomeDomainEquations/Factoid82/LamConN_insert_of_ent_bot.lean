/-ai
Inserting bottom that is entailed at stage n preserves consistency at stage n.

Entailment of bottom gives consistency of the original finset, and inserting bottom preserves that consistency.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntN_con
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN_insert_bot

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)



























theorem LamConN_insert_of_ent_bot {n : ℕ} {u : Finset (RawLamToken α)}
    (ht : LamEntN A n u .bot) : LamConN A n (insert (.bot : RawLamToken α) u) :=
  LamConN_insert_bot A (LamEntN_con A ht)

end InfoSys
end DomainTheory.InformationSystems
