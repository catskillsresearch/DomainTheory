/-ai
Equality of sum tokens is decidable. Two left constructors reduce to equality of the underlying tokens of α, two right constructors reduce to equality of the underlying tokens of β, and two bottom constructors are equal. A left constructor differs from a right constructor and from bottom, a right constructor differs from a left constructor and from bottom, and bottom differs from either injection.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

instance instDecidableEqSumToken : DecidableEq (SumToken α β)
  | .left a, .left b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.left.inj h')
  | .right a, .right b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.right.inj h')
  | .bot, .bot => isTrue rfl
  | .left _, .right _ => isFalse fun h => nomatch h
  | .left _, .bot => isFalse fun h => nomatch h
  | .right _, .left _ => isFalse fun h => nomatch h
  | .right _, .bot => isFalse fun h => nomatch h
  | .bot, .left _ => isFalse fun h => nomatch h
  | .bot, .right _ => isFalse fun h => nomatch h

end InfoSys

end DomainTheory.InformationSystems
