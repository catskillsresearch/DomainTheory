/-ai
Two approximable maps with the same relation are equal.

The two relations are equal as functions by functional extensionality and propositional extensionality. Substituting that equality makes the remaining data agree, so the structures are identical.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Extensionality for the relation.** Two approximable maps with the same neighbourhood relation
are equal (the remaining fields are propositions). -/
theorem ext {f g : ApproximableMap V₀ V₁} (h : ∀ X Y, f.rel X Y ↔ g.rel X Y) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y; exact propext (h X Y)
  subst this; rfl

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
