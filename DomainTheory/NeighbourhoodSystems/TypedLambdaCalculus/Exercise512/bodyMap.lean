module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The body of the loop as a two-argument map `M : (D → D) × D → D`,
`M(w, x) = cond(p(x), w(f(x)), x)`. It is assembled from `cond`, `eval`, the projections,
pairing and composition, hence approximable. -/
def bodyMap : ApproximableMap (prod (funSpace V V) V) V :=
  (cond V).comp
    (paired (p.comp (proj₁ (funSpace V V) V))
      (paired
        ((evalMap V V).comp
          (paired (proj₀ (funSpace V V) V) (f.comp (proj₁ (funSpace V V) V))))
        (proj₁ (funSpace V V) V)))

end DomainTheory.NeighbourhoodSystems.Exercise512
