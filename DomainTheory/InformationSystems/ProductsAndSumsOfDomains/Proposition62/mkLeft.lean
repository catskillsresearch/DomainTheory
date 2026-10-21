/-ai
The left tag of a token x of A is the product token with components x and the bottom token of B, witnessed by the right disjunct of the product-token condition. Scott writes this token as (X, Δ_B).
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

/-- Left-tagged product token `(X, Δ_B)`. -/
def mkLeft (x : α) : ProdToken A B :=
  ⟨(x, B.bot), Or.inr rfl⟩

end InfoSys

end DomainTheory.InformationSystems
