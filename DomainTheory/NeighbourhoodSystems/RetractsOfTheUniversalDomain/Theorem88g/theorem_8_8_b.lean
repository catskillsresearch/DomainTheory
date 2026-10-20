module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_inj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_proj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_projectionPair_isComputable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88g.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

/-- **Theorem 8.8(b) (Scott 1981, PRG-19), final assembly.** If `D` is effectively given (via a
`ComputablePresentation P`), the general universality of `U` (Theorem 8.8(a)) can be witnessed by a
`D' : NeighborhoodSystem ℚ` that is *itself* effectively given (`P' : ComputablePresentation D'`),
isomorphic to `D`, a subsystem of `U`, **and** whose projection pair `i := (D' ◁ U).inj`,
`j := (D' ◁ U).proj` (Proposition 6.12) is computable in both directions relative to `P'` and `U`'s
own presentation `UComputablePresentation`. -/
theorem theorem_8_8_b {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D) :
    ∃ (D' : NeighborhoodSystem ℚ) (P' : ComputablePresentation D') (h : D' ◁ U),
      (D ≅ᴰ D') ∧
        IsComputableMap P' UComputablePresentation h.inj ∧
        IsComputableMap UComputablePresentation P' h.proj :=
  ⟨DprimeUCode P, DprimeUCodePresentation P, DprimeUCode_subsystem P,
    isomorphic_DprimeUCode P, DprimeUCode_inj_isComputableMap P, DprimeUCode_proj_isComputableMap P⟩

end DomainTheory.NeighbourhoodSystems
