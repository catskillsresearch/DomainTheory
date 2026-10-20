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
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.exists_rel_of_subset_image

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

/-- **Definition 5.2.** Image of an element under an approximable mapping. -/
def toElement (f : ApproximableMap A B) (x : A.Element) : B.Element where
  carrier := {Y | ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y}}
  consistent := by
    intro Y hY
    obtain ⟨u, _, hrel⟩ := exists_rel_of_subset_image f x Y hY
    exact f.rel_cod hrel
  closed := by
    intro Y a hY hEnt
    obtain ⟨u, hu, hrel⟩ := exists_rel_of_subset_image f x Y hY
    have harel : f.rel u {a} :=
      f.mono hrel (proposition_2_3_iii A (f.rel_dom hrel))
        (fun z hz => by
          rw [Finset.mem_singleton] at hz
          rw [hz]
          exact hEnt)
        (f.rel_dom hrel) (B.con_sing a)
    exact ⟨u, hu, harel⟩

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
