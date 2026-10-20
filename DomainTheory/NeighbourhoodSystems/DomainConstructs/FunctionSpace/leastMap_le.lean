module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.rel_interYs

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}








































/-- **Proposition 3.9 (Scott 1981, PRG-19).** `f₀` is the *minimal* element of the neighbourhood:
any `f` with `Xᵢ f Yᵢ` for all `i` satisfies `f₀ ⊆ f`. -/
theorem leastMap_le {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {f : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) : leastMap L hL hcons ≤ f := by
  rintro X Y ⟨hX, hY, hsub⟩
  exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

end DomainTheory.NeighbourhoodSystems
