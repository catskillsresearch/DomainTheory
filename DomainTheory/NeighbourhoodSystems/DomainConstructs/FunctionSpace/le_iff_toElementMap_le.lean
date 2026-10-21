/-ai
One approximable map lies below another if and only if its value at every element lies below the other map's value.

If the relation of the first is contained in the second, an output of the first at an element, witnessed by an input in that element, is an output of the second. Conversely, a related pair of the first is membership of the output in the first map at the principal filter of the input, hence in the second map, which is the relation of the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Theorem 3.13(i) (Scott 1981, PRG-19).** `f ⊑ g ↔ ∀ x, f(x) ⊑ g(x)`. -/
theorem le_iff_toElementMap_le {f g : ApproximableMap V₀ V₁} :
    f ≤ g ↔ ∀ x, f.toElementMap x ≤ g.toElementMap x := by
  constructor
  · intro h x Y ⟨X, hXx, hrel⟩
    exact ⟨X, hXx, h X Y hrel⟩
  · intro h X Y hrel
    have hX : V₀.mem X := f.rel_dom hrel
    rw [f.rel_iff_mem_principal hX] at hrel
    rw [g.rel_iff_mem_principal hX]
    exact h (V₀.principal hX) Y hrel

end DomainTheory.NeighbourhoodSystems
