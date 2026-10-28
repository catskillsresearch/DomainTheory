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
