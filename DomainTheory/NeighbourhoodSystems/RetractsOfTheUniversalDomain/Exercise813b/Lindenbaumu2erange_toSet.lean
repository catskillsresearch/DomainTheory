/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.generatedBy_iff_exists_evalSet

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


















/-- **Headline: `Lindenbaum.toSet`'s range is exactly `Exercise813a.lean`'s free Boolean algebra on
`ℵ₀` generators, `{X | GeneratedBy generator X}`.** Together with injectivity, `Lindenbaum.toSet`
is a bijection `Lindenbaum ≃ {X : Set ℕ // GeneratedBy generator X}` — i.e. `Lindenbaum` *is* (a
faithful copy of) the algebra `8.13(a)` already showed `U ≅ᴰ`'s domain of proper filters is built
from. This is exactly `8.13`'s parenthetical: "the free Boolean algebra on `ℵ₀`-generators
(= the Lindenbaum algebra of propositional calculus)." -/
theorem Lindenbaum.range_toSet : Set.range Lindenbaum.toSet = {X | GeneratedBy generator X} := by
  ext X
  simp only [Set.mem_range, Set.mem_ofPred_eq, generatedBy_iff_exists_evalSet]
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.ind with
    | _ φ => exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨⟦φ⟧, rfl⟩

end DomainTheory.NeighbourhoodSystems
