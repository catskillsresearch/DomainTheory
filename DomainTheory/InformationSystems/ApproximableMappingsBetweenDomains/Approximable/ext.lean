/-ai
Two approximable mappings are equal whenever they relate exactly the same pairs of finite sets.

The underlying relations agree by functional and propositional extensionality. Substituting that agreement leaves the two structure packages identical.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ApproximableMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

theorem ext {f g : ApproximableMap A B} (h : ∀ u v, f.rel u v ↔ g.rel u v) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by
    funext u v
    exact propext (h u v)
  subst this
  rfl

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
