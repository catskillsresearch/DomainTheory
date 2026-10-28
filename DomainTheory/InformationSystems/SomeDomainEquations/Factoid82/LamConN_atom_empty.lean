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

theorem LamConN_atom_empty {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hne : lamFunFinset u ≠ ∅) : lamAtomFinset u = ∅ := by
  induction n generalizing u with
  | zero => exact False.elim (hne hu.2)
  | succ n ih =>
    rcases hu with hu | ⟨hA, _, _⟩
    · exact ih hu hne
    · exact hA

end InfoSys
end DomainTheory.InformationSystems
