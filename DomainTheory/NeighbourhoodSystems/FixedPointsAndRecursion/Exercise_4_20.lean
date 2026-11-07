module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixComp

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
open ApproximableMap

theorem example_420 {α : Type*} {V : NeighborhoodSystem α}
    (f g : ApproximableMap V V) : (f.comp g).fixElement = f.toElementMap (g.comp f).fixElement :=
  @fixElement_comp_comm α V f g

end DomainTheory.NeighbourhoodSystems.ApproximableMap
