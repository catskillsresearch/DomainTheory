/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88f

@[expose] public section

/-!
# Theorem 8.8(b)(viii) — final assembly

`Theorem88e.lean` (Part 7(3)) built `D'' := DprimeUCode P`, the isomorphism `D ≅ᴰ D''`
(`isomorphic_DprimeUCode`), the subsystem relation `D'' ◁ U` (`DprimeUCode_subsystem`), and `D''`'s
own `ComputablePresentation` (`DprimeUCodePresentation`); `Theorem88f.lean` (Part 7(4)) showed the
projection pair witnessing `D'' ◁ U` (Proposition 6.12's `inj`/`proj`) is computable relative to
`DprimeUCodePresentation`/`UComputablePresentation`
(`DprimeUCode_projectionPair_isComputable`). This file packages all of it into the single headline
statement of **Theorem 8.8(b)**: if `D` is effectively given, the projection pair witnessing
`D ⊴ U` (Theorem 8.8(a)) can be taken computable.

No new mathematical content — every ingredient already exists; this is exactly `theorem_8_8_a`'s
statement (`Theorem88a.lean`) with `D'` replaced by a presented `D'` and the projection pair
additionally asserted computable.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive
end DomainTheory.Neighborhood
