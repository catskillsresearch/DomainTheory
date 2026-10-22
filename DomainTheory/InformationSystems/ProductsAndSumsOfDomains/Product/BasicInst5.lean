/-ai
This instance decides whether a pair is a product token. The pair qualifies when its first component is the least token of the first system, and otherwise when its second component is the least token of the second system. If neither component is least, both alternatives fail.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.IsProdToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

instance (A : InfoSys α) (B : InfoSys β) (p : α × β) : Decidable (IsProdToken A B p) :=
  if h1 : p.1 = A.bot then isTrue ⟨Or.inl h1⟩
  else if h2 : p.2 = B.bot then isTrue ⟨Or.inr h2⟩
  else isFalse fun h => h.out.elim h1 h2

end InfoSys

end DomainTheory.InformationSystems
