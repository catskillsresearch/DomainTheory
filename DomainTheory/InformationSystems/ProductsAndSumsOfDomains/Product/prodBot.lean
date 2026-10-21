/-ai
The least token of a product is the pair of the two least tokens. That pair is a product token because its first component is least.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Product bottom `Δ_{A×B} = (Δ_A, Δ_B)`. -/
def prodBot : ProdToken A B :=
  ⟨(A.bot, B.bot), Or.inl rfl⟩

end InfoSys

end DomainTheory.InformationSystems
