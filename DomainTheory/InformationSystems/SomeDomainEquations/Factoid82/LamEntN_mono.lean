/-ai
Stage-n entailment of a raw lambda token persists at every later stage.

The proof inducts on the inequality of stages. At equal stages the entailment is unchanged. A successor step places the inductive result in the previous-stage disjunct of the successor clause.
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

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)




















theorem LamEntN_mono {n m : ℕ} (hmn : n ≤ m) {u : Finset (RawLamToken α)}
    {t : RawLamToken α} (ht : LamEntN A n u t) : LamEntN A m u t := by
  induction hmn with
  | refl => exact ht
  | step _ ih => exact Or.inl ih

end InfoSys
end DomainTheory.InformationSystems
