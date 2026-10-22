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


theorem LamEntN_con {n : ℕ} {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : LamEntN A n u t) : LamConN A n u := by
  match n, t with
  | 0, .bot => exact ht
  | 0, .atom _ => exact ht.1
  | 0, .funTok _ _ => exact False.elim ht
  | n + 1, t =>
    rcases ht with ht | ht
    · exact Or.inl (LamEntN_con (n := n) ht)
    · match t with
      | .bot => exact ht
      | .atom _ => exact ht.1
      | .funTok _ _ => exact ht.1

end InfoSys
end DomainTheory.InformationSystems
