/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
