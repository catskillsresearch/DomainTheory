module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.lucidHistory

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.LucidHistory
/-- Scott's Exercise 7.24: L is effectively given; lifted connectives and toElement. -/
theorem example_724 :
    L.IsEffectivelyGiven ∧
    ComputableMap LTpres LTpres (postcompose notT) ∧
    ComputableMap (prodPresentation LTpres LTpres) LTpres (pointwiseBin andT) ∧
    Function.Bijective toElement :=
  ⟨L_isEffectivelyGiven, ⟨notT_lifted_isComputable, ⟨andT_lifted_isComputable, toElement_bijective⟩⟩⟩

