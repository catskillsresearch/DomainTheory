/-ai
Two approximable maps that induce the same function on elements are equal.

Extensionality of the relation splits on whether the input is a neighbourhood. When it is, each relation is membership of the output in the elementwise image of the corresponding principal element, and those images agree. When it fails to be a neighbourhood, neither relation holds, because a related input is a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.rel_iff_mem_principal

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}



namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}




/-- **Proposition 2.2(iv) (Scott 1981, PRG-19).** Two approximable maps are *identical as relations*
iff they induce the same elementwise function: `(∀ x, f(x) = g(x)) ⟹ f = g`. For neighbourhoods `X`
the relation is read off `f(↑X)` (`rel_iff_mem_principal`); off `𝒟₀` both relations are empty. -/
theorem ext_of_toElementMap {f g : ApproximableMap V₀ V₁}
    (h : ∀ x, f.toElementMap x = g.toElementMap x) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
