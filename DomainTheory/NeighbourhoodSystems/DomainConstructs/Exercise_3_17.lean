module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.embBinSeq

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem BitDom ApproximableMap
open DomainTheory.NeighbourhoodSystems.EmbBinSeq
/-- Scott's Exercise 3.17: embedding of binary sequences with a left inverse. -/
theorem example_317 :
    f.comp g ≤ idMap (iterSys T) ∧ g.comp f = idMap B :=
  ⟨fg_le_id, gf_eq_id⟩

