/-ai
This file gathers Definition 8.1 and Proposition 6.12 and re-exports the subsystem retraction, the order isomorphism between the elements of a subsystem and the fixed points of that retraction, the neighbourhood relation of the retraction, and the fact that the retraction fixes the image of the injection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition81
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.elementIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem_toElementMap_inj

@[expose] public section

/-!
# Lecture VIII — Proposition 8.2 (Scott 1981, PRG-19): `D ◁ E` induces a retraction

**Proposition 8.2.** If `D ◁ E` and `a : E → E` is defined by

`X a Z` iff `∃ Y ∈ D. X ⊆ Y ⊆ Z`

for all `X, Z ∈ E`, then `a` is a retraction and `|D|` is isomorphic to the fixed-point set of `a`,
`{y ∈ |E| ∣ a(y) = y}`, under inclusion.

## The construction

Scott's own proof observes that the relation above is exactly `a = i ∘ j`, where `i : D → E`,
`j : E → D` are the injection/projection of Proposition 6.12 (`Subsystem.inj`/`Subsystem.proj`).
We take this as the *definition* (`retractionOfSubsystem`), which makes both halves of the theorem
short calculations with the category laws of Theorem 2.5:

* **`a` is a retraction.** `a ∘ a = i∘j∘i∘j = i∘(j∘i)∘j = i∘I_D∘j = i∘j = a`, using
  `Subsystem.proj_comp_inj : j ∘ i = I_D` (`isRetraction_retractionOfSubsystem`).
* **`|D| ≅ Fix(a)`.** The forward map `x ↦ i(x)` lands in `Fix(a)` because
  `a(i(x)) = i(j(i(x))) = i((j∘i)(x)) = i(x)`; the inverse is `y ↦ j(y)`, using
  `Subsystem.proj_comp_inj` again for the round trip `j(i(x)) = x`, and the fixed-point equation
  `a(y) = y` itself (unfolded to `i(j(y)) = y`) for the other round trip. Both `i` and `j` are
  monotone, and applying `j` to `i(x) ⊑ i(x')` recovers `x ⊑ x'` (again via `j ∘ i = I_D`), so the
  correspondence is an order-isomorphism, not just a bijection (`elementIso`).

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`), since Proposition 6.12
and Theorem 2.5 are.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem


end Subsystem
end DomainTheory.NeighbourhoodSystems
