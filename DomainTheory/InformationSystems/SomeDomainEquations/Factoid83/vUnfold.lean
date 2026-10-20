module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- Unfold product-shaped tokens into `V × V`. Top `∇` has no single product-token
image (it generates the top *element*); we send it to `(∇, Δ)` as a left witness. -/
def vUnfold (t : VToken) : ProdToken vSystem vSystem :=
  match t with
  | .bot => prodBot vSystem vSystem
  | .top => ⟨(.top, .bot), Or.inr rfl⟩
  | .pairL x => ⟨(x, .bot), Or.inr rfl⟩
  | .pairR y => ⟨(.bot, y), Or.inl rfl⟩

end InfoSys

end DomainTheory.InformationSystems
