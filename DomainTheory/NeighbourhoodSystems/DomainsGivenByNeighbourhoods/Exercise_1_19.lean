module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
/- concordance: source L468 EXERCISE 1.19 positive neighbourhood systems -/
/-- **Exercise 1.19 (Scott 1981, PRG-19) — positivity, condition (ii′).** A neighbourhood
system is *positive* when Scott's (ii) is strengthened to the biconditional **(ii′)**: for
`X, Y ∈ 𝒟`, the intersection `X ∩ Y` is a neighbourhood **iff** it is non-empty. -/
def NeighborhoodSystem.IsPositive {α : Type*} (V : NeighborhoodSystem α) : Prop :=
  ∀ ⦃X Y : Set α⦄, V.mem X → V.mem Y → (V.mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)

/-- Scott's *"very special circumstance"* (the prose after Examples 1.2–1.4): a family `𝒟`
is **nested-or-disjoint** when any two of its members are either nested (one included in the
other) or disjoint. -/
def NestedOrDisjoint {α : Type*} (mem : Set α → Prop) : Prop :=
  ∀ ⦃X Y : Set α⦄, mem X → mem Y → X ⊆ Y ∨ Y ⊆ X ∨ X ∩ Y = ∅

end DomainTheory.NeighbourhoodSystems
end
