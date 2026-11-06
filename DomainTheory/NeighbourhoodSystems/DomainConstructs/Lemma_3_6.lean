module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.constMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
open ApproximableMap

/-- Scott's Lemma 3.6: the constant approximable map at an ideal element has the membership
    relation of that element, and acts elementwise as the constant function. -/
theorem lemma_3_6 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {b : V₁.Element} {X : Set α} {Y : Set β},
      (constMap V₀ b).rel X Y ↔ V₀.mem X ∧ b.mem Y) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (b : V₁.Element) (x : V₀.Element),
      (constMap V₀ b).toElementMap x = b) :=
  ⟨@constMap_rel, @toElementMap_constMap⟩

end DomainTheory.NeighbourhoodSystems
