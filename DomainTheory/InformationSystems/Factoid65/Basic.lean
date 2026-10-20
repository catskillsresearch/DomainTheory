/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Proposition56
public import DomainTheory.InformationSystems.Factoid33

@[expose] public section

/-!
# Factoid 6.5 — the unit domain

**Scott 1982 (end of §6, after Prop 6.2).** The trivial product of no factors is the
*unit* information system `1` with `D_1 = {Δ_1}`. It has a unique element `⊥_1`.
Every approximable map `1 → A` is constant, and there is a unique approximable map
`A → 1`, namely `const(⊥_1)`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- **Factoid 6.5.** The unit information system on a singleton token type. -/
def unitSystem : InfoSys PUnit where
  bot := ⟨⟩
  Con := Set.univ
  Ent := fun _ _ => True
  con_subset := by
    intro u v _ _
    exact trivial
  con_sing := by
    intro _
    exact trivial
  ent_con := by
    intro u a _
    exact trivial
  ent_bot := by
    intro u _
    exact trivial
  ent_refl := by
    intro u a _ _
    exact trivial
  ent_trans := by
    intro u v c _ _ _ _
    exact trivial

namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}
end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
