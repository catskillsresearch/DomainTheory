module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)














/-- **Theorem 1.10 (statement).** Any neighbourhood system is isomorphic to its element-token
system: `𝒟 ≅ᴰ {[X]}`. -/
theorem isomorphic_tokenSystem : V ≅ᴰ V.tokenSystem := ⟨V.tokenIso⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
