/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition62
public import DomainTheory.InformationSystems.Factoid32

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- Product element `⟨x, y⟩` assembled from the two projections. -/
def pairElements (x : A.Element) (y : B.Element) : (productSystem A B).Element where
  carrier := {p : ProdToken A B |
    (p.val.2 = B.bot → p.val.1 ∈ x.carrier) ∧ (p.val.1 = A.bot → p.val.2 ∈ y.carrier)}
  consistent := by
    intro Y hY
    refine ⟨?_, ?_⟩
    · have hsub : ↑(fstFinset A B Y) ⊆ x.carrier := by
        intro a ha
        rcases (mem_fstFinset A B).1 ha with ⟨p, hp, hbot, rfl⟩
        exact (hY (Finset.mem_coe.2 hp)).1 hbot
      exact x.consistent _ hsub
    · have hsub : ↑(sndFinset A B Y) ⊆ y.carrier := by
        intro b hb
        rcases (mem_sndFinset A B).1 hb with ⟨p, hp, hbot, rfl⟩
        exact (hY (Finset.mem_coe.2 hp)).2 hbot
      exact y.consistent _ hsub
  closed := by
    intro Y p hY hEnt
    obtain ⟨hCon, hL, hR⟩ := hEnt
    refine ⟨?_, ?_⟩
    · intro hbot
      have hEntA : A.Ent (fstFinset A B Y) p.val.1 := hL hbot
      have hsub : ↑(fstFinset A B Y) ⊆ x.carrier := by
        intro a ha
        rcases (mem_fstFinset A B).1 ha with ⟨q, hq, hbot', rfl⟩
        exact (hY (Finset.mem_coe.2 hq)).1 hbot'
      exact x.closed _ _ hsub hEntA
    · intro hbot
      have hEntB : B.Ent (sndFinset A B Y) p.val.2 := hR hbot
      have hsub : ↑(sndFinset A B Y) ⊆ y.carrier := by
        intro b hb
        rcases (mem_sndFinset A B).1 hb with ⟨q, hq, hbot', rfl⟩
        exact (hY (Finset.mem_coe.2 hq)).2 hbot'
      exact y.closed _ _ hsub hEntB

end InfoSys

end DomainTheory.InformationSystems
