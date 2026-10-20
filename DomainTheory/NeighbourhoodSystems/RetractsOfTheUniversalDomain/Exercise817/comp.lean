/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.ProjPair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- **`ProjPair`s compose.** If `D ⇄ E` and `E ⇄ F` are projection pairs, so is `D ⇄ F`
(`inj := p2.inj ∘ p1.inj`, `proj := p1.proj ∘ p2.proj`). The first law composes as an equality
chain; the second only needs `≤`, transported through `comp_mono_gen`. -/
def ProjPair.comp {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    {F : NeighborhoodSystem γ} (p1 : ProjPair D E) (p2 : ProjPair E F) :
    ProjPair D F where
  inj := p2.inj.comp p1.inj
  proj := p1.proj.comp p2.proj
  proj_comp_inj := by
    show (p1.proj.comp p2.proj).comp (p2.inj.comp p1.inj) = idMap D
    rw [comp_assoc, ← comp_assoc p2.proj p2.inj p1.inj, p2.proj_comp_inj, idMap_comp,
      p1.proj_comp_inj]
  inj_comp_proj_le := by
    show (p2.inj.comp p1.inj).comp (p1.proj.comp p2.proj) ≤ idMap F
    rw [comp_assoc, ← comp_assoc p1.inj p1.proj p2.proj]
    calc p2.inj.comp ((p1.inj.comp p1.proj).comp p2.proj)
        ≤ p2.inj.comp ((idMap E).comp p2.proj) :=
          comp_mono_gen le_rfl (comp_mono_gen p1.inj_comp_proj_le le_rfl)
      _ = p2.inj.comp p2.proj := by rw [idMap_comp]
      _ ≤ idMap F := p2.inj_comp_proj_le

end DomainTheory.NeighbourhoodSystems
