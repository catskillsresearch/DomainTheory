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


theorem LamConN_mono {n m : ℕ} (hmn : n ≤ m) {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) : LamConN A m u := by
  induction hmn with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

end InfoSys
end DomainTheory.InformationSystems
