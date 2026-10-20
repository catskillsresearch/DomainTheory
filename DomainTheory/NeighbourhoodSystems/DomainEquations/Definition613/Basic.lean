module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.MonotoneAt
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.MonotoneOnDomains
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.targetFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.ContinuousOnDomains

@[expose] public section

/-!
# Lecture VI — Definition 6.13 (Scott 1981, PRG-19): functors *monotone / continuous on domains*

> **DEFINITION 6.13.** A functor `T` is *monotone on domains* iff whenever `D ◁ E`, then not only do
> we have `T(D) ◁ T(E)` but the projection pair `i, j` of 6.12 is mapped to the same kind of
> projection pair `T(i), T(j)`. A monotone functor is *continuous on domains* iff whenever `E` is a
> domain, then the mapping `λD. T(D) : {D ∣ D ◁ E} → {D' ∣ D' ◁ T(E)}` is approximable.

This is the second of Scott's two continuity conditions on a functor (the first being Definition 6.8,
*continuous on maps*). Together with a generating set `Γ` they power the existence Theorem 6.14
(initial `T`-algebras as iterated-functor colimits `𝒟 = ⋃ₙ Tⁿ({Γ})`).

## What the formalization uses

* **The functor.** `T` is an `Endofunctor DomainObj` (Definition 6.3), acting on objects (`T.obj`)
  and on the approximable maps between them (`T.map`).
* **The subdomain relation `◁`.** Definition 6.10 (`Subsystem`), between two systems over the *same*
  token type, with the projection pair `i = Subsystem.inj`, `j = Subsystem.proj` of Proposition 6.12.
* **The domain of subsystems `{D ∣ D ◁ E}`.** Proposition 6.11 shows this *is* a domain; here it is
  the subtype `{D // D ◁ E}` and the directed-union sups are the union subsystems `unionSys`.

### The carrier-type subtlety, and how it is handled

`D ◁ E` requires `D, E` to be systems over a *common* token type `α`. The abstract functor `T` need
not preserve token types: `T.obj ⟨α, D⟩` and `T.obj ⟨α, E⟩` may have different carriers. So
"`T(D) ◁ T(E)`" only makes sense once we *assert* that `T` preserves the token type along `◁`, i.e.
once the carriers of the two images agree. **Monotone on domains** therefore packages, for each
`h : D ◁ E`:

* `carrier_eq`: the two image carriers coincide;
* `sub`: the transported subdomain relation `T(D) ◁ T(E)`;
* `inj_heq`/`proj_heq`: Scott's "the projection pair `i, j` is mapped to `T(i), T(j)`", i.e. the
  canonical 6.12 pair of `T(D) ◁ T(E)` is exactly `(T.map i, T.map j)` (stated up to the carrier
  transport, hence `HEq`).

**Continuous on domains** then adds Scott's approximability of `λD. T(D)`, rendered in the concrete
neighbourhood framework as *preservation of directed unions of subsystems*: for any directed family
`ℱ` of subsystems of `E` whose union is the subsystem `U`, the (target-side) neighbourhood family of
`T(U)` is the union of those of the `T(D)`. This is exactly the continuity Scott invokes in the proof
of 6.14 (`T(⋃ₙ Tⁿ{Γ}) = ⋃ₙ T(Tⁿ⁺¹{Γ})`).

The identity functor is monotone and continuous on domains (`monotoneOnDomains_id`,
`continuousOnDomains_id`), witnessing non-vacuity. Everything is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe w

/-! ### Monotone on domains -/



/-! ### Continuous on domains -/


end DomainTheory.NeighbourhoodSystems
