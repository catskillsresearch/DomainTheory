/-ai
A token belongs to the image of an element under an approximable mapping if and only if some finite set of tokens contained in the element is related to the singleton of that token.

The two sides are the same membership condition in the carrier of the image, so the equivalence is definitional.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ext
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.singleton_funion_eq
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.exists_rel_of_subset_image

@[expose] public section

/-!
# Approximable mappings — Definitions 5.1 and 5.2

Adapted from the PRG-19 approximable-map pattern, rewritten for Scott 1982
information systems (relations on `Con × Con`).
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]


namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}


@[simp] theorem mem_toElement (f : ApproximableMap A B) (x : A.Element) {Y : β} :
    Y ∈ (f.toElement x).carrier ↔ ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y} :=
  Iff.rfl
end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
