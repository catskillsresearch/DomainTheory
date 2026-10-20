/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise818.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **Exercise 8.18 (Scott 1981, PRG-19), in full: Proposition 8.10, both halves, all three
combinators.** If `a, b : 𝒰 → 𝒰` are projections, then so are `a+b`, `a×b`, `a→b`
(`isProjection_combinators`); if moreover `a, b` are finitary, then so are `a+b`, `a×b`, `a→b`
(`finitaryProjection_combinators`) — and (packaged inside `IsFinitaryProjection`'s `IsFinitary`
witness) the fixed-point set of each is isomorphic to the corresponding construct applied to `D_a`,
`D_b` (`sumComb_elementIso`/`prodComb_elementIso`/`arrowComb_elementIso` in `Proposition810b.lean`).
No case of Proposition 8.10 is left unestablished. -/
theorem exercise_8_18 {a b : ApproximableMap U U} (ha : IsProjection a) (hb : IsProjection b) :
    (IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b)) ∧
      (IsFinitaryProjection a → IsFinitaryProjection b →
        IsFinitaryProjection (sumComb a b) ∧ IsFinitaryProjection (prodComb a b) ∧
          IsFinitaryProjection (arrowComb a b)) :=
  ⟨isProjection_combinators ha hb, fun hfa hfb => finitaryProjection_combinators hfa hfb⟩

end DomainTheory.NeighbourhoodSystems
