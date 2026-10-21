/-ai
If two self-maps of the universal domain lie below the identity, then their lambda combinator lies below the identity of the function space.

Compare elements, and pass across the function-space equivalence. Transporting the lambda combinator sends a map to the second map composed after it composed after the first. Monotonicity of composition in each factor, using the two inequalities below the identity, reduces this to the map composed with the two identities, which is the map itself.
ai-/
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


/-- **Proposition 8.10, `→`-case (the `lamComb` half), projection.** -/
theorem le_idMap_lamComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    lamComb a b ≤ idMap (funSpace U U) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap, ← (funSpaceEquiv U U).le_iff_le, funSpaceEquiv_apply,
    funSpaceEquiv_apply, toApproxMap_toElementMap_lamComb]
  calc b.comp ((toApproxMap φ).comp a) ≤ (idMap U).comp ((toApproxMap φ).comp (idMap U)) :=
        comp_mono_gen hb (comp_mono_gen le_rfl ha)
    _ = toApproxMap φ := by rw [comp_idMap, idMap_comp]

end DomainTheory.NeighbourhoodSystems
