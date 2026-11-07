module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.embBinSeq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise317
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem BitDom ApproximableMap

/-- Scott's Exercise 3.17: embedding of binary sequences with a left inverse. -/
theorem example_317 :
    f.comp g ≤ idMap (iterSys T) ∧ g.comp f = idMap B :=
  ⟨fg_le_id, gf_eq_id⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
