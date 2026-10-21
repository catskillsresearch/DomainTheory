/-ai
The order isomorphism between the elements of a neighbourhood system and the elements of its element-token system sends an element to its token and a token back to its element. In the left round trip, a neighbourhood of the composite is a neighbourhood whose bracket equals the bracket of a neighbourhood of the original element, hence the same neighbourhood by injectivity of brackets, while in the other direction the neighbourhood itself is the witness. In the right round trip, a neighbourhood of the composite is a bracket already belonging to the token, and a neighbourhood of the token is a bracket of some neighbourhood by the subfamily law. If the token of the first element lies below the token of the second, a neighbourhood of the first has a bracket belonging to the second token, and injectivity of brackets returns the neighbourhood. Conversely, a bracket of a neighbourhood of the first is a bracket of a neighbourhood of the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.mem_bracket
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.bracket_injective
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.tokenSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.tokenSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.toToken
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.ofToken

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Theorem 1.10 (the isomorphism).** `X ↦ [X]` induces an order-isomorphism `|𝒟| ≃o |{[X]}|`:
`toToken` and `ofToken` are mutually inverse and preserve/reflect `⊑`. -/
def tokenIso : V.Element ≃o V.tokenSystem.Element where
  toFun := V.toToken
  invFun := V.ofToken
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨hX, X', hX', heq⟩
      rw [V.bracket_injective hX (x.sub hX') heq]; exact hX'
    · intro hx
      exact ⟨x.sub hx, X, hx, rfl⟩
  right_inv := by
    intro y
    apply Element.ext
    intro S
    constructor
    · rintro ⟨X, ⟨_, hyX⟩, rfl⟩
      exact hyX
    · intro hyS
      obtain ⟨X, hX, rfl⟩ := y.sub hyS
      exact ⟨X, ⟨hX, hyS⟩, rfl⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hx
      have hmem : (V.toToken x).mem (V.bracket X) := ⟨X, hx, rfl⟩
      obtain ⟨X', hX', heq⟩ := h (V.bracket X) hmem
      rw [V.bracket_injective (x.sub hx) (x'.sub hX') heq]; exact hX'
    · intro h S hS
      obtain ⟨X, hX, rfl⟩ := hS
      exact ⟨X, h X hX, rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
