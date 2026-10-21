/-ai
A raw lambda token over a carrier is the bottom token, an atom drawn from the carrier, or a function token given by an input list and an output list of raw lambda tokens.

Boolean equality of raw tokens, and of lists of raw tokens, is defined mutually. Bottom matches only bottom, atoms match when their carriers match, function tokens match when both lists match, and every other combination fails. Two lists match when they are both empty or when their heads match and their tails match.

Boolean equality of raw tokens holds exactly when the tokens are equal, and boolean equality of lists holds exactly when the lists are equal.

The two statements are proved together by recursion on the tokens and the lists. Both bottoms agree. Two atoms agree by equality of their carriers and injectivity of the atom constructor. Two function tokens agree by the list statement together with injectivity of the function-token constructor. Distinct constructors make the boolean test fail and make equality impossible. Two empty lists agree, two nonempty lists agree by the token statement on the heads and the list statement on the tails, and a mismatch of empty against nonempty fails.

Decidable equality of raw lambda tokens tests this boolean equality and uses the equivalence with propositional equality.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
variable {α : Type*} [DecidableEq α]

inductive RawLamToken (α : Type*) where
  | bot : RawLamToken α
  | atom : α → RawLamToken α
  | funTok : List (RawLamToken α) → List (RawLamToken α) → RawLamToken α

mutual
  def rawLamBEq : RawLamToken α → RawLamToken α → Bool
    | .bot, .bot => true
    | .atom x, .atom y => decide (x = y)
    | .funTok u v, .funTok u' v' => rawLamListBEq u u' && rawLamListBEq v v'
    | _, _ => false
  def rawLamListBEq : List (RawLamToken α) → List (RawLamToken α) → Bool
    | [], [] => true
    | x :: xs, y :: ys => rawLamBEq x y && rawLamListBEq xs ys
    | _, _ => false
end

mutual
  theorem rawLamBEq_eq : ∀ a b : RawLamToken α, rawLamBEq a b = true ↔ a = b
  | .bot, .bot => by simp [rawLamBEq]
  | .atom x, .atom y => by
      simp only [rawLamBEq, decide_eq_true_eq]
      exact ⟨congrArg RawLamToken.atom, RawLamToken.atom.inj⟩
  | .funTok u v, .funTok u' v' => by
      simp only [rawLamBEq, Bool.and_eq_true]
      constructor
      · intro ⟨hu, hv⟩
        rw [(rawLamListBEq_eq u u').1 hu, (rawLamListBEq_eq v v').1 hv]
      · intro h
        injection h with hu hv
        subst hu; subst hv
        exact ⟨(rawLamListBEq_eq u u).2 rfl, (rawLamListBEq_eq v v).2 rfl⟩
  | .bot, .atom _ | .bot, .funTok _ _ | .atom _, .bot | .atom _, .funTok _ _
  | .funTok _ _, .bot | .funTok _ _, .atom _ => by
      constructor
      · intro h; simp [rawLamBEq] at h
      · intro h; cases h
  theorem rawLamListBEq_eq : ∀ u v : List (RawLamToken α), rawLamListBEq u v = true ↔ u = v
  | [], [] => by simp [rawLamListBEq]
  | x :: xs, y :: ys => by
      simp only [rawLamListBEq, Bool.and_eq_true]
      constructor
      · intro ⟨hx, hxs⟩
        rw [(rawLamBEq_eq x y).1 hx, (rawLamListBEq_eq xs ys).1 hxs]
      · intro h
        injection h with hx hxs
        subst hx; subst hxs
        exact ⟨(rawLamBEq_eq x x).2 rfl, (rawLamListBEq_eq xs xs).2 rfl⟩
  | [], _ :: _ | _ :: _, [] => by
      constructor
      · intro h; simp [rawLamListBEq] at h
      · intro h; cases h
end

instance : DecidableEq (RawLamToken α) := fun a b =>
  if h : rawLamBEq a b = true then isTrue ((rawLamBEq_eq a b).1 h)
  else isFalse fun hab => h ((rawLamBEq_eq a b).2 hab)

end InfoSys
end DomainTheory.InformationSystems
