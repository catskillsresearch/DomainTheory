module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofMono

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open ApproximableMap


/-- Scott's Exercise 2.8: approximable maps are determined by their action on principal
filters, and every monotone assignment of elements to neighbourhoods arises that way. -/
theorem exercise_2_8 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {f g : ApproximableMap V₀ V₁},
      (∀ (X : Set α) (hX : V₀.mem X),
        f.toElementMap (V₀.principal hX) = g.toElementMap (V₀.principal hX)) →
      f = g) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (m : (X : Set α) → V₀.mem X → V₁.Element)
      (hmono : ∀ (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X'),
        X' ⊆ X → m X hX ≤ m X' hX')
      (X : Set α) (hX : V₀.mem X),
      (ofMono m hmono).toElementMap (V₀.principal hX) = m X hX) :=
  ⟨fun {_ _} {_ _} {_ _} => eq_of_toElementMap_principal,
    fun {_ _} {_ _} => toElementMap_ofMono_principal⟩

