/-ai
The LUCID neighbourhood system is effectively given. The digit map from bits to natural numbers is injective. The elements of L are exactly the finite or infinite sequences of natural numbers: the map from sequences to elements is bijective.

The numbered name example_724 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_isEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toElement_bijective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

set_option linter.unusedVariables false

theorem example_724 : And
  (And
    (And
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
        DomainTheory.NeighbourhoodSystems.Exercise724.Gamma DomainTheory.NeighbourhoodSystems.Exercise724.L)
      (@DomainTheory.NeighbourhoodSystems.IsComputableMap
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
        (@DomainTheory.NeighbourhoodSystems.Exercise724.postcompose DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example23.T
          DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.notT)))
    (@DomainTheory.NeighbourhoodSystems.IsComputableMap
      (Sum
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prod
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres)
      DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
      (@DomainTheory.NeighbourhoodSystems.Exercise724.pointwiseBin DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Example23.T
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.andT)))
  (@Function.Bijective DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
      DomainTheory.NeighbourhoodSystems.Exercise724.L)
    DomainTheory.NeighbourhoodSystems.Exercise724.toElement) :=
  @And.intro
  (And
    (And
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
        DomainTheory.NeighbourhoodSystems.Exercise724.Gamma DomainTheory.NeighbourhoodSystems.Exercise724.L)
      (@DomainTheory.NeighbourhoodSystems.IsComputableMap
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
        (@DomainTheory.NeighbourhoodSystems.Exercise724.postcompose DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example23.T
          DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.notT)))
    (@DomainTheory.NeighbourhoodSystems.IsComputableMap
      (Sum
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prod
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres)
      DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
      (@DomainTheory.NeighbourhoodSystems.Exercise724.pointwiseBin DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Example23.T
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.andT)))
  (@Function.Bijective DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
      DomainTheory.NeighbourhoodSystems.Exercise724.L)
    DomainTheory.NeighbourhoodSystems.Exercise724.toElement)
  (@And.intro
    (And
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
        DomainTheory.NeighbourhoodSystems.Exercise724.Gamma DomainTheory.NeighbourhoodSystems.Exercise724.L)
      (@DomainTheory.NeighbourhoodSystems.IsComputableMap
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
        (@DomainTheory.NeighbourhoodSystems.Exercise724.postcompose DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example23.T
          DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.notT)))
    (@DomainTheory.NeighbourhoodSystems.IsComputableMap
      (Sum
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prod
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres)
      DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
      (@DomainTheory.NeighbourhoodSystems.Exercise724.pointwiseBin DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Example23.T
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.andT))
    (@And.intro
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
        DomainTheory.NeighbourhoodSystems.Exercise724.Gamma DomainTheory.NeighbourhoodSystems.Exercise724.L)
      (@DomainTheory.NeighbourhoodSystems.IsComputableMap
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
        (@DomainTheory.NeighbourhoodSystems.Exercise724.postcompose DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example23.T
          DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.notT))
      DomainTheory.NeighbourhoodSystems.Exercise724.L_isEffectivelyGiven
      DomainTheory.NeighbourhoodSystems.Exercise724.notT_lifted_isComputable)
    DomainTheory.NeighbourhoodSystems.Exercise724.andT_lifted_isComputable)
  DomainTheory.NeighbourhoodSystems.Exercise724.toElement_bijective

end DomainTheory.NeighbourhoodSystems.Exercise724
