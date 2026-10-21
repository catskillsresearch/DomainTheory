/-ai
The map sending an element to the filter of brackets of its neighbourhoods is a bijection onto the elements of the token system.

That map is the underlying function of the order isomorphism between the two domains, and an order isomorphism is bijective.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)




/-- **Exercise 1.21 — tokens ↔ elements.** `toToken : |𝒟| → |{[X]}|` is a bijection (it is the
underlying map of the order-iso `tokenIso`), so a complete system identifies tokens with
(partial) elements under a one-one correspondence. -/
theorem tokenSystem_toToken_bijective : Function.Bijective V.toToken :=
  V.tokenIso.bijective

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
