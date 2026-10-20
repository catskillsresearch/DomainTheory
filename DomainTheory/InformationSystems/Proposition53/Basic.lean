/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Approximable

/-!
# Proposition 5.3 — images, order, and the closure bridge

**Scott 1982, Proposition 5.3.** Remaining clauses after Def 5.2 / `toElement`:
singleton reduction (Scott’s remark before Def 5.2); (v) the bridge
`u f v ↔ v̄ ⊆ f(ū)`; (iii) pointwise order; (ii) extensionality via elements.
(i) and (iv) are already `toElement` / `toElement_mono` in `Approximable.lean`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {A : InfoSys α} {B : InfoSys β}

def Le (f g : ApproximableMap A B) : Prop := ∀ ⦃u v⦄, f.rel u v → g.rel u v
end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
