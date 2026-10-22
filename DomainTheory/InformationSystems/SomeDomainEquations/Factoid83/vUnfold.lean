/-ai
Unfolding sends a token of V to a product token of V × V. The bottom token unfolds to the product bottom. The top token has no single product-token image, because it generates the top element, and is sent to the pair of the top token with the bottom token, as a left witness. A left-pair token with payload x unfolds to the pair of x with the bottom token, and a right-pair token with payload y unfolds to the pair of the bottom token with y.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vSystem

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- Unfold product-shaped tokens into `V × V`. Top `∇` has no single product-token
image (it generates the top *element*); we send it to `(∇, Δ)` as a left witness. -/
def vUnfold (t : VToken) : ProdToken vSystem vSystem :=
  match t with
  | .bot => prodBot vSystem vSystem
  | .top => ⟨(.top, .bot), ⟨Or.inr rfl⟩⟩
  | .pairL x => ⟨(x, .bot), ⟨Or.inr rfl⟩⟩
  | .pairR y => ⟨(.bot, y), ⟨Or.inl rfl⟩⟩

end InfoSys

end DomainTheory.InformationSystems
