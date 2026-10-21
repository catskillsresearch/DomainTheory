/-ai
The section induced by an order isomorphism from the fixed set of an approximable endomap a to the elements of a neighbourhood system F sends a principal neighbourhood of F to the underlying element of E obtained by applying the inverse isomorphism to that principal. Monotonicity on principals is the monotonicity of that inverse, rewritten by the order of principals.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.FixSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.fixedNbhd_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.BasicInst8

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section HardDirection

variable {a : ApproximableMap E E}

variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)

/-- **The section `i : F → E`** induced by the abstract witness `e` of `IsFinitary a`: on the
principal element `↑X` of `F`, `i` returns the underlying `E`-element of `e.symm(↑X) ∈ Fix(a)`.
Built via `ofMono` (Exercise 2.8) — monotone on principals is all that's needed. -/
def sectionMap : ApproximableMap F E :=
  ofMono (fun _X hX => (e.symm (F.principal hX)).1) (fun _ _ hX hX' hXX' =>
    e.symm.monotone ((F.principal_le_iff hX hX').mpr hXX'))

end HardDirection

end DomainTheory.NeighbourhoodSystems
