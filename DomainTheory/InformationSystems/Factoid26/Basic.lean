/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InfoSys

public import DomainTheory.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.Factoid26.Consistent
public import DomainTheory.InformationSystems.Factoid26.Ent
public import DomainTheory.InformationSystems.Factoid26.partialFunctionSystem
public import DomainTheory.InformationSystems.Factoid26.consistent_singleton
public import DomainTheory.InformationSystems.Factoid26.consistent_subset
public import DomainTheory.InformationSystems.Factoid26.consistent_insert_bot
public import DomainTheory.InformationSystems.Factoid26.consistent_insert_mem

@[expose] public section

/-!
# Factoid 2.6 — third example: partial-function graphs plus `Δ`

**Scott 1982, §2 (“A third example”).** Fix sets `A` and `B`. Data objects are pairs
`(a, b) ∈ A × B` (meaning “the function maps `a` to `b`”) together with a least-informative
`Δ`. A finite set of pairs is consistent iff it is functional:

```
{(aᵢ, bᵢ)} ∈ Con  iff  (aᵢ = aⱼ → bᵢ = bⱼ for all i, j);
```

adjoining `Δ` preserves consistency. Entailment is the minimal one:

```
u ⊢ X  iff  X = Δ  ∨  X ∈ u.
```
-/

namespace DomainTheory.InformationSystems

namespace Factoid26








example : InfoSys (Token ℕ Bool) := partialFunctionSystem ℕ Bool
end Factoid26
end DomainTheory.InformationSystems
