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





















theorem LamConN_atom_con {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hne : lamAtomFinset u ≠ ∅) : lamAtomFinset u ∈ A.Con := by
  induction n generalizing u with
  | zero => exact hu.1
  | succ n ih =>
    rcases hu with hu | ⟨hA, _, _⟩
    · exact ih hu hne
    · exact False.elim (hne hA)

end InfoSys
end DomainTheory.InformationSystems
