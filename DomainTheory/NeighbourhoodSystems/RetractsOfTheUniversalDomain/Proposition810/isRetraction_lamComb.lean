module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toApproxMap_toElementMap_lamComb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



/-- **Proposition 8.10, `→`-case (the `lamComb` half), retraction.** -/
theorem isRetraction_lamComb {a b : ApproximableMap U U} (ha : IsRetraction a)
    (hb : IsRetraction b) : IsRetraction (lamComb a b) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_comp,
    toApproxMap_toElementMap_lamComb a b ((lamComb a b).toElementMap φ),
    toApproxMap_toElementMap_lamComb a b φ,
    comp_assoc b ((toApproxMap φ).comp a) a,
    ← comp_assoc b b (((toApproxMap φ).comp a).comp a), hb,
    comp_assoc (toApproxMap φ) a a, ha]

end DomainTheory.NeighbourhoodSystems
