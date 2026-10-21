/-ai
The approximable endomaps fixed by sub are order-isomorphic to the subsystems of E. The forward map sends a fixed map to its fixed neighbourhood system, and the backward map sends a subsystem to its retraction, which is fixed by sub. The left inverse is the fixed-point equation. The right inverse recovers the subsystem from the retraction it induces. A subsystem inclusion of the fixed neighbourhood systems lifts a relation of sub by applying the inclusion to the witness neighbourhood, and the two fixed-point equations turn that into an inequality of the maps. An inequality of the maps, read as a comparison of subsystems of a common master, holds because a self-related neighbourhood of the smaller map remains self-related for the larger map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.fixedNbhd_retractionOfSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_retractionOfSubsystem

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.fixedNbhd_subsystem
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **The finitary projections on `E` are order-isomorphic to the subsystems of `E`.** Forward:
`f ↦ ⟨fixedNbhd f, fixedNbhd_subsystem f⟩`; backward: `D ↦ retractionOfSubsystem D` (a fixed point
of `sub`, by `sub_retractionOfSubsystem`). Round trips are `fixedNbhd_retractionOfSubsystem` and
(definitionally) `sub`'s own defining equation; order is preserved/reflected via `sub`'s formula
being monotone in the underlying subsystem (`retractionOfSubsystem_rel`'s witness clause) together
with `Subsystem.subsystem_iff_subset_of_common`. -/
def finitaryProjectionSubsystemEquiv (E : NeighborhoodSystem α) :
    {f : ApproximableMap E E // sub f = f} ≃o {D : NeighborhoodSystem α // D ◁ E} where
  toFun f := ⟨fixedNbhd f.1, fixedNbhd_subsystem f.1⟩
  invFun D := ⟨Subsystem.retractionOfSubsystem D.2, sub_retractionOfSubsystem D.2⟩
  left_inv f := Subtype.ext f.2
  right_inv D := Subtype.ext (fixedNbhd_retractionOfSubsystem D.2)
  map_rel_iff' := by
    intro f g
    constructor
    · intro hle
      have hleD : fixedNbhd f.1 ◁ fixedNbhd g.1 := hle
      have hsub : sub f.1 ≤ sub g.1 := by
        rintro X Z hXZ
        rw [sub_rel] at hXZ ⊢
        obtain ⟨hX, hZ, Y, hY, hXY, hYZ⟩ := hXZ
        exact ⟨hX, hZ, Y, hleD.sub hY, hXY, hYZ⟩
      rwa [f.2, g.2] at hsub
    · intro hfg
      show fixedNbhd f.1 ◁ fixedNbhd g.1
      refine (Subsystem.subsystem_iff_subset_of_common
        (fixedNbhd_subsystem f.1) (fixedNbhd_subsystem g.1)).mpr ?_
      intro X hX
      exact ⟨hX.1, hfg X X hX.2⟩

end DomainTheory.NeighbourhoodSystems
