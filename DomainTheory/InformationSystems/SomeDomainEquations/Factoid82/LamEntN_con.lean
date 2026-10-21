/-ai
Stage-n entailment of a raw lambda token implies stage-n consistency of the finite set.

The proof matches on the stage and the token. At stage zero, entailment of bottom is the consistency, entailment of an atom projects its consistency component, and entailment of a function token is impossible. At a successor stage, the previous-stage disjunct reduces by a recursive call at that stage, and the new disjunct projects the consistency component of bottom, of an atom, or of a function token.
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
