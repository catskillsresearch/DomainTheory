/-ai
Theorem 8.6 states that the packaged map subApprox on the function space is finitary: its fixed elements are order-isomorphic to a domain.

The witness is the composite of the order isomorphism from the fixed elements of subApprox to the endomaps fixed by sub, the order isomorphism from those endomaps to the subsystems of E, and the representation of the subsystems of E as a domain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.finitaryProjectionSubsystemEquiv
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subApprox
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subApproxFixIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.fixedNbhd_retractionOfSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_retractionOfSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toFilter_toApproxMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_toFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_injective
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_monotone
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_rel_iSupDirected
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_toApproxMap_iSupDirected
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter_iSupDirected
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter_monotone
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.continuous_subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toElementMap_subApprox

public import DomainTheory.NeighbourhoodSystems.DomainEquations.subsystemReprIso
@[expose] public section

/-!
# Lecture VIII — Theorem 8.6 (Scott 1981, PRG-19): the `sub` combinator

**Theorem 8.6.** For any domain `E` define `sub : (E → E) → (E → E)` by the formula

`X sub(f) Z` iff `∃Y ∈ E. X ⊆ Y, f Y ⊆ Z`,

for all `X, Z ∈ E` and all `f : E → E`. Then the range of `sub` consists exactly of the finitary
projections on `E`, and moreover `sub` itself is a finitary projection on `(E → E)`. If `E` is
effectively given, then `sub` is computable.

## What is formalized here

Scott's formula for `sub(f)` is *literally* Proposition 8.2's `retractionOfSubsystem`, applied to
Theorem 8.5's subdomain `D = fixedNbhd f = {Y ∈ E ∣ Y f Y}` (which, recall, is a genuine subsystem
`D ◁ E` for *any* `f`, no hypotheses needed). This module formalizes the per-token map
`sub : ApproximableMap E E → ApproximableMap E E` and its order-theoretic content at that level,
**Theorem 8.6's clause 1 in full**:

* **`sub f ≤ f`** (`sub_le`) — Scott's "`X ⊆ Y, f Y ⊆ Z` always implies `X f Z`", a bare
  monotonicity calculation, valid for *any* `f`.
* **`sub` is idempotent, exactly: `sub (sub f) = sub f`** (`sub_sub`) — sharper than Scott's stated
  inclusion `sub(f) ⊆ sub(sub(f))`: unwinding `fixedNbhd (sub f)` shows it has *the same*
  neighbourhoods as `fixedNbhd f` (`Y ⊆ Y' ⊆ Y` forces `Y = Y'`), so `sub (sub f)` and `sub f` are
  built from literally the same subsystem and hence are equal, not just related by `≤`.
* **`sub` is monotone** (`sub_mono`) — immediate from `fixedNbhd`'s definition.
* **`range(sub) = finitary projections`, both directions** (`sub_eq_self_iff_isFinitaryProjection`):
  the easy half `sub f = f → IsFinitaryProjection f` (`isFinitaryProjection_of_sub_eq_self`) is
  immediate substitution into `Subsystem.isFinitaryProjection_retractionOfSubsystem`; the converse
  `IsFinitaryProjection f → sub f = f` (`sub_eq_self_of_isFinitaryProjection`) is now unblocked by
  Theorem 8.5's hard direction (`formula_of_isFinitaryProjection`): `sub_le` gives `⊇` for free, and
  `⊆` unwinds `X f Z` via `rel_iff_mem_principal` into `Z ∈ f(↑X)`, then rewrites via Theorem 8.5's
  formula into exactly `sub_rel`'s defining shape.
* **`sub f` is *always* a finitary projection**, for any `f` (`isFinitaryProjection_sub`) —
  `sub (sub f) = sub f` plus the above.

**Theorem 8.6's clause 2, in full (in `namespace Sub8_6`):** `sub` packaged as a genuine
`ApproximableMap (funSpace E E) (funSpace E E)` (`subApprox`), realizing Scott's remark that
"the correspondence `f ↦ sub(f)` preserves directed unions of `f`'s, thus `sub` is itself
approximable", and shown to be a **finitary projection** on `(E → E)`
(`isFinitaryProjection_subApprox`):
`subApprox` is built via Exercise 2.13's `ofContinuous`, using a new general domain-theory bridge
`continuous_of_monotone_iSupDirected` (`Exercise213.lean`: monotone + directed-sup-preserving ⟹
topologically continuous, proved directly from algebraicity) applied to `subFilter`, `sub`
transported along `funSpaceEquiv`. `subFilter`'s directed-sup-preservation
(`subFilter_iSupDirected`) needs no consistency argument at all: directed unions of *filters*
correspond, under `toApproxMap`, to the raw union of the underlying maps' *relations*
(`toApproxMap_rel_iSupDirected`, immediate from `mem_iSupDirected`), and `sub`'s formula is a
*positive* existential in `f`'s relation, hence commutes with such unions by pure logic
(`sub_toApproxMap_iSupDirected`). `IsRetraction subApprox`/`subApprox ≤ idMap` then drop out of
`sub_sub`/`sub_le` respectively (`isProjection_subApprox`).

**`IsFinitary subApprox`** (`isFinitary_subApprox`) turned out *not* to need the universal-domain
machinery after all: `finitaryProjectionSubsystemEquiv` upgrades Theorem 8.6(a)'s bijection
`f ↦ fixedNbhd f` / `D ↦ retractionOfSubsystem D` between `{f ∣ sub f = f}` and the subsystems
`{D ∣ D ◁ E}` into a genuine **order-isomorphism** (round trips `fixedNbhd_retractionOfSubsystem`
and `sub`'s own defining equation; order via `retractionOfSubsystem_rel`'s witness clause plus
`Subsystem.subsystem_iff_subset_of_common`). Composed with `Fix(subApprox) ≃o {f ∣ sub f = f}`
(`subApproxFixIso`, via `toApproxMap`/`toFilter`) and **Lecture VI's Proposition 6.11**
(`subsystemReprIso`: the subsystems of `E` already form a genuine domain), this gives the witness
for `IsFinitary subApprox` directly, with no new "domain of subsystems" construction needed.

**Not formalized (deferred):**

* **Clause 3 (computability)** — needs `E` effectively given (Def 7.1 machinery); a separate,
  not-yet-formalized prerequisite.

Everything proved here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`), *except*
`isFinitary_subApprox`/`isFinitaryProjection_subApprox`, which pick up `Classical.choice` solely
through Proposition 6.11's `subsystemReprIso` (itself inheriting it from Exercise 2.22's `reprIso`,
the documented "for set theorists" exercise) — the same, already-accepted, provenance as every
other domain-representation result in this project (Ex 3.25/3.27, Prop 6.11 itself).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




/-! ## The finitary-projections-on-`E` ↔ subsystems-of-`E` order-isomorphism

Needed below for `Sub8_6.isFinitary_subApprox` (Theorem 8.6(b)(ii)): the bijection `f ↦ fixedNbhd f`
/ `D ↦ retractionOfSubsystem D` between `{f ∣ sub f = f}` (the finitary projections) and
`{D ∣ D ◁ E}` (the subsystems) that already underlies `sub`'s definition is in fact an
order-isomorphism. Composed with Proposition 6.11's `subsystemReprIso` (the subsystems of `E`
already form a genuine domain, from Lecture VI), this gives Theorem 8.6(b)(ii)'s witness directly —
no new "domain of subsystems" construction is needed here. -/




/-! ## Theorem 8.6, clause 2 (partial): `sub` is itself approximable, and a projection, on
`(E → E)`

Scott's remark: "the correspondence `f ↦ sub(f)` preserves directed unions of `f`'s, thus `sub`
is itself approximable". We realize this via Exercise 2.13 (`ofContinuous`): transported along
`funSpaceEquiv` to `subFilter : (funSpace E E).Element → (funSpace E E).Element`, `sub` is monotone
(`subFilter_mono`, from `sub_mono`) and preserves directed unions (`subFilter_iSupDirected`) — the
latter because `sub`'s defining formula (`sub_rel`) is a *positive* existential in `f`'s relation,
so it commutes with the raw union of relations that `toApproxMap` assigns to a directed union of
filters (`toApproxMap_rel_iSupDirected`, immediate from `mem_iSupDirected`), with no extra
consistency argument needed. `continuous_of_monotone_iSupDirected` then upgrades this to genuine
topological continuity, giving `subApprox := ofContinuous subFilter hc`.

`IsFinitary subApprox` (further below) needs no new "domain of subsystems" construction: it
composes `Fix(subApprox) ≃o {f ∣ sub f = f}` (`subApproxFixIso`) with the
`finitaryProjectionSubsystemEquiv`/`subsystemReprIso` route already available from Theorem 8.6(a)
and Lecture VI's Proposition 6.11.

**Not yet formalized:** the computability clause (Theorem 8.6's clause 3), which needs `E`
effectively given (Def 7.1 machinery), a separate prerequisite. -/

namespace Sub8_6















/-! ### Theorem 8.6(b)(ii): `subApprox` is finitary

`Fix(subApprox)` is order-isomorphic to `{f ∣ sub f = f}` (the finitary projections on `E`, via
`toApproxMap`/`toFilter`), which in turn is order-isomorphic to the subsystems of `E`
(`finitaryProjectionSubsystemEquiv`, just above) — and Proposition 6.11 already exhibits the
subsystems of `E` as a genuine domain (`subsystemReprIso`). No new "domain of subsystems"
construction is needed: it was already built in Lecture VI. -/


/-- **Theorem 8.6(b)(ii) (Scott 1981, PRG-19).** `subApprox` is finitary: composing
`subApproxFixIso` with `finitaryProjectionSubsystemEquiv` and Proposition 6.11's
`subsystemReprIso` witnesses `Fix(subApprox)` as (order-isomorphic to) a genuine domain. -/
theorem isFinitary_subApprox : IsFinitary (subApprox (E := E)) :=
  ⟨_, _, ⟨subApproxFixIso.trans
    ((finitaryProjectionSubsystemEquiv E).trans (Proposition611.subsystemReprIso E))⟩⟩
end Sub8_6
end DomainTheory.NeighbourhoodSystems
