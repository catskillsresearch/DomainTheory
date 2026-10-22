/-ai
An element of Pω is combinatory if and only if it is generated from G.

Zero is generated from G because G applied to G equals zero. The successor is generated from G by its projection from G and zero, and the numeral 1 is the successor applied to zero. Predecessor, conditional, K, and S are generated from G by their projections from G, zero, and the numeral 1. Application preserves generation from G, so every combinatory element is generated from G. Conversely, G is combinatory, and application preserves the combinatory property.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_app_self
public import DomainTheory.DataTypesAsLattices.Enumeration.sucC_from_G
public import DomainTheory.DataTypesAsLattices.Enumeration.predC_from_G
public import DomainTheory.DataTypesAsLattices.Enumeration.condC_from_G
public import DomainTheory.DataTypesAsLattices.Enumeration.Kcomb_from_G
public import DomainTheory.DataTypesAsLattices.Enumeration.Scomb_from_G
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.sucC_zero

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem theorem_3_1 {u : Pomega} :
    IsCombinatory u ↔ GeneratedFromG u := by
  have hzero : GeneratedFromG zeroC := by
    simpa [Gcomb_app_self] using
      GeneratedFromG.app GeneratedFromG.G GeneratedFromG.G
  constructor
  · intro hu
    have hsuc : GeneratedFromG sucC := by
      simpa [sucC_from_G] using
        GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hzero
    have hone : GeneratedFromG (ofNat 1) := by
      simpa [sucC_zero] using GeneratedFromG.app hsuc hzero
    induction hu with
    | zero => exact hzero
    | suc => exact hsuc
    | pred =>
      simpa [predC_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone) hzero
    | cond =>
      simpa [condC_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone) hone)
          hzero
    | K =>
      simpa [Kcomb_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app
              (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone)
                hone)
            hone)
          hzero
    | S =>
      simpa [Scomb_from_G] using
        GeneratedFromG.app
          (GeneratedFromG.app
            (GeneratedFromG.app
              (GeneratedFromG.app (GeneratedFromG.app GeneratedFromG.G hzero) hone)
                hone)
            hone)
          hone
    | app _ _ iu iv => exact .app iu iv
  · intro hu
    induction hu with
    | G => exact Gcomb_combinatory
    | app _ _ iu iv => exact .app iu iv

end DomainTheory.DataTypesAsLattices
