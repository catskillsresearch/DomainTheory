module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.isomorphic_DprimeUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.DprimeUCode_isEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_inj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_proj_isComputableMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Theorem 8.8(b)(vii)(4), full statement.** The projection pair witnessing `D'' ◁ U` (Proposition
6.12, applied to `DprimeUCode_subsystem P : DprimeUCode P ◁ U`) is computable in both directions
relative to `D''`'s own presentation (`DprimeUCodePresentation`) and `U`'s presentation
(`UComputablePresentation`) — the headline claim of Theorem 8.8(b)(vii). -/
theorem DprimeUCode_projectionPair_isComputable :
    ComputableMap (DprimeUCodePresentation P) UComputablePresentation
        (DprimeUCode_subsystem P).inj ∧
      ComputableMap UComputablePresentation (DprimeUCodePresentation P)
        (DprimeUCode_subsystem P).proj :=
  ⟨DprimeUCode_inj_isComputableMap P, DprimeUCode_proj_isComputableMap P⟩

end DomainTheory.NeighbourhoodSystems
