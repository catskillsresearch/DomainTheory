/-ai
If D is effectively given, then the subsystem built from the re-pointed enumeration is effectively given.

The witness is the computable presentation of that subsystem.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88c.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)



















/-- **Theorem 8.8(b), Part 6.** If `D` is effectively given, then Theorem 8.8(a)'s own subsystem
`D'` (with `D ≅ᴰ D'` and `D' ◁ U`, from `isomorphic_DprimeU`/`DprimeU_subsystem`) is *also*
effectively given. -/
theorem DprimeU_isEffectivelyGiven :
    (DprimeU D (e P) (hcover P) (he0 P)).IsEffectivelyGiven :=
  ⟨DprimeUPresentation P⟩

end DomainTheory.NeighbourhoodSystems
