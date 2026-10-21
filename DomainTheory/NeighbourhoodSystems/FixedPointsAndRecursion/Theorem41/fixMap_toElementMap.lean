/-ai
The elementwise value of the fixed-point operator at a function-space element equals the least fixed point of the approximable map corresponding to that element.

Extensionality and the principal form of membership split the equality into two inclusions. From a witnessing neighbourhood of the function-space element, the operator on the corresponding principal returns the least fixed point of its least map, that principal lies below the element by upward closure, and monotonicity of the function-space equivalence and of the least fixed point moves the neighbourhood into the desired fixed point. In the other direction a finite chain from the master factors through some neighbourhood of the element, and the principal clause turns that factored chain into membership in the operator value.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_toElementMap_principal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.exists_principal_iterMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- **Theorem 4.2 (Scott 1981, PRG-19) — Scott's equation (∗).** The elementwise action of `fix` is
the least fixed point of the corresponding map: `fix.toElementMap φ = fix(toApproxMap φ)`. The
forward inclusion (`⊆ x`) is `exists_principal_iterMap`; the reverse is monotonicity of `fix` along
`↑W ⊑ toApproxMap φ`. -/
theorem fixMap_toElementMap (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (fixMap V).toElementMap φ = (toApproxMap φ).fixElement := by
  apply Element.ext
  intro X
  rw [toElementMap_mem_iff_principal]
  constructor
  · rintro ⟨W, hw, hmem⟩
    rw [fixMap_toElementMap_principal] at hmem
    have hle : (funSpace V V).principal (φ.sub hw) ≤ φ :=
      fun Z hZ => φ.up_mem hw hZ.1 hZ.2
    exact fixElement_mono ((funSpaceEquiv V V).monotone hle) X hmem
  · rintro ⟨n, hn⟩
    obtain ⟨W, hw, hWn⟩ := exists_principal_iterMap V φ n X hn
    refine ⟨W, hw, ?_⟩
    rw [fixMap_toElementMap_principal]
    exact ⟨n, hWn⟩

end DomainTheory.NeighbourhoodSystems
