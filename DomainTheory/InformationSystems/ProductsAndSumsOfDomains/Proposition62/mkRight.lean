/-ai
The right tag of a token y of B is the product token with components the bottom token of A and y, witnessed by the left disjunct of the product-token condition. Scott writes this token as (Δ_A, Y).
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

/-- Right-tagged product token `(Δ_A, Y)`. -/
def mkRight (y : β) : ProdToken A B :=
  ⟨(A.bot, y), Or.inl rfl⟩

end InfoSys

end DomainTheory.InformationSystems
