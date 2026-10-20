module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.myStep_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.myFoldl_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.myFoldl_inter_of_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.D_inter_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.D_X_inter_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.D_X_inter_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88m.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88m.fixedNbhd_isEffectivelyGiven

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Theorem 8.8(c) (Scott 1981, PRG-19), headline.** If `a : U → U` is a computable, finitary
projection of the universal domain, then `{Y ∈ U ∣ Y a Y}` is effectively given (and, unconditionally
by Theorem 8.5, a subsystem of `U`). As in Theorem 8.6(c)'s converse, `hfin` is carried in the
signature to match Scott's stated hypothesis on `a`, but is **not** actually needed by this
implication — only `hcomp` drives the effectiveness argument; this is called out here rather than
silently dropping the hypothesis. -/
theorem theorem_8_8_c {a : ApproximableMap U U} (_hfin : IsFinitaryProjection a)
    (hcomp : IsComputableMap UComputablePresentation UComputablePresentation a) :
    (fixedNbhd a).IsEffectivelyGiven ∧ fixedNbhd a ◁ U :=
  ⟨fixedNbhd_isEffectivelyGiven hcomp, fixedNbhd_subsystem a⟩

end DomainTheory.NeighbourhoodSystems
