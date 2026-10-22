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


theorem LamConN_empty (n : ℕ) : LamConN A n (∅ : Finset (RawLamToken α)) := by
  induction n with
  | zero =>
    change lamAtomFinset ∅ ∈ A.Con ∧ lamFunFinset ∅ = ∅
    rw [lamAtomFinset_empty, lamFunFinset_empty]
    exact ⟨A.con_empty, rfl⟩
  | succ n ih => exact Or.inl ih

end InfoSys
end DomainTheory.InformationSystems
