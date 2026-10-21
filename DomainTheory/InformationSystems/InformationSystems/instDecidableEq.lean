/-ai
This instance decides equality of interval tokens. The two least-informative tokens are equal. A least-informative token and an interval fall under different constructors, so they are unequal. Two intervals are equal exactly when their endpoints agree: equal endpoints give equality of the tokens, and an equality of tokens injects onto the endpoints. The proofs of the strict inequalities are ignored.
ai-/
module

public import Mathlib.Algebra.Order.Field.Rat
import all Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
import all Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
import all Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid25.Token

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid25

namespace Token

/-- Decidable equality ignores the `<` proof (proof-irrelevant). -/
instance instDecidableEq : DecidableEq Token
  | bot, bot => isTrue rfl
  | bot, interval _ _ _ => isFalse Token.noConfusion
  | interval _ _ _, bot => isFalse Token.noConfusion
  | interval n m _, interval n' m' _ =>
    if h : n = n' ∧ m = m' then
      isTrue (by
        rcases h with ⟨rfl, rfl⟩
        rfl)
    else
      isFalse (by
        intro hEq
        injection hEq with hn hm
        exact h ⟨hn, hm⟩)

end Token

end Factoid25

end DomainTheory.InformationSystems
