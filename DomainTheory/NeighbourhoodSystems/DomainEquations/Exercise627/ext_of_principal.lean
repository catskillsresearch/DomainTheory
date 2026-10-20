module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}






variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

















section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










/-- Choice-free extensionality from agreement on principal inputs. Unlike `ext_of_toElementMap`
(which splits on the undecidable `V₀.mem X`), both sides of the relation carry domain membership via
`rel_dom`, so no case analysis — and hence no `Classical.choice` — is needed. -/
theorem ext_of_principal {γ δ : Type*} {W₀ : NeighborhoodSystem γ} {W₁ : NeighborhoodSystem δ}
    {f g : ApproximableMap W₀ W₁}
    (h : ∀ (X : Set γ) (hX : W₀.mem X),
      f.toElementMap (W₀.principal hX) = g.toElementMap (W₀.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  constructor
  · intro hr
    have hX := f.rel_dom hr
    rw [g.rel_iff_mem_principal hX, ← h X hX, ← f.rel_iff_mem_principal hX]; exact hr
  · intro hr
    have hX := g.rel_dom hr
    rw [f.rel_iff_mem_principal hX, h X hX, ← g.rel_iff_mem_principal hX]; exact hr

end Part5
end Exercise627
end DomainTheory.NeighbourhoodSystems
