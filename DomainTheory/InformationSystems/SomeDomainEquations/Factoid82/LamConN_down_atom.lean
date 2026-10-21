/-ai
A finset with no function tokens that is consistent at stage n is consistent at stage zero.

Induct on the stage. Stage zero is the hypothesis. At a successor stage, the left alternative uses the inductive hypothesis, and the right alternative has an empty atom finset, so together with the empty function-token projection it is stage-zero consistency by emptiness of the consistent sets of A.
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





















/-- Atom/bot-only sets that are consistent at stage `n` are consistent at stage `0`. -/
theorem LamConN_down_atom {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hF : lamFunFinset u = ∅) : LamConN A 0 u := by
  induction n generalizing u with
  | zero => exact hu
  | succ n ih =>
    rcases hu with hu | ⟨hA, _, _⟩
    · exact ih hu hF
    · exact ⟨by rw [hA]; exact A.con_empty, hF⟩

end InfoSys
end DomainTheory.InformationSystems
