module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.graphFun

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise723
open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

/-- Scott's Exercise 7.23: the graph map is computable. -/
theorem example_723 (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf PNpres PNpres (decodeList c))
      : Set (ApproximableMap PN PN)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ PNpres.X s.unpair.1 ⊆ PNpres.X s.unpair.2)
    (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ PNpres.X s.unpair.1 = PNpres.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    ComputableMap
      (funPresentation PNpres PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p
        heq1 heq1p)
      PNpres graphMap :=
  graphMap_isComputable gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p heq1 heq1p

end DomainTheory.NeighbourhoodSystems.Exercise723

