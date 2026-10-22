/-ai
The graph map is computable from an arbitrary valid function-space presentation of PNpres into PNpres. Its neighbourhood relation reduces to a bounded quantification over the excluded set of the output neighbourhood, which is recursively enumerable.

The numbered name example_723 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.graphMap_isComputable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise723

set_option linter.unusedVariables false

theorem example_723 : ∀ (gN incl0 incl1 eq1 : Nat → Nat)
  (hgN :
    ∀ (c : Nat),
      Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Set.Nonempty
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Nat Nat DomainTheory.NeighbourhoodSystems.Example78.PN
            DomainTheory.NeighbourhoodSystems.Example78.PN)
          (@DomainTheory.NeighbourhoodSystems.stepFun Nat Nat DomainTheory.NeighbourhoodSystems.Example78.PN
            DomainTheory.NeighbourhoodSystems.Example78.PN
            (@DomainTheory.NeighbourhoodSystems.funListOf Nat Nat DomainTheory.NeighbourhoodSystems.Example78.PN
              DomainTheory.NeighbourhoodSystems.Example78.PN DomainTheory.NeighbourhoodSystems.Example78.PNpres
              DomainTheory.NeighbourhoodSystems.Example78.PNpres (Domain.Recursive.decodeList c)))))
  (hgNp : Nat.Primrec gN)
  (hincl0 :
    ∀ (s : Nat),
      Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@LE.le (Set Nat) (@Set.instLE Nat)
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X Nat
            DomainTheory.NeighbourhoodSystems.Example78.PN DomainTheory.NeighbourhoodSystems.Example78.PNpres
            (@Prod.fst Nat Nat (Nat.unpair s)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X Nat
            DomainTheory.NeighbourhoodSystems.Example78.PN DomainTheory.NeighbourhoodSystems.Example78.PNpres
            (@Prod.snd Nat Nat (Nat.unpair s)))))
  (hincl0p : Nat.Primrec incl0)
  (hincl1 :
    ∀ (s : Nat),
      Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@LE.le (Set Nat) (@Set.instLE Nat)
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X Nat
            DomainTheory.NeighbourhoodSystems.Example78.PN DomainTheory.NeighbourhoodSystems.Example78.PNpres
            (@Prod.fst Nat Nat (Nat.unpair s)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X Nat
            DomainTheory.NeighbourhoodSystems.Example78.PN DomainTheory.NeighbourhoodSystems.Example78.PNpres
            (@Prod.snd Nat Nat (Nat.unpair s)))))
  (hincl1p : Nat.Primrec incl1)
  (heq1 :
    ∀ (s : Nat),
      Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq (Set Nat)
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X Nat
            DomainTheory.NeighbourhoodSystems.Example78.PN DomainTheory.NeighbourhoodSystems.Example78.PNpres
            (@Prod.fst Nat Nat (Nat.unpair s)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X Nat
            DomainTheory.NeighbourhoodSystems.Example78.PN DomainTheory.NeighbourhoodSystems.Example78.PNpres
            (@Prod.snd Nat Nat (Nat.unpair s)))))
  (heq1p : Nat.Primrec eq1),
  @DomainTheory.NeighbourhoodSystems.ComputableMap
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Nat Nat DomainTheory.NeighbourhoodSystems.Example78.PN
      DomainTheory.NeighbourhoodSystems.Example78.PN)
    Nat
    (@DomainTheory.NeighbourhoodSystems.funSpace Nat Nat DomainTheory.NeighbourhoodSystems.Example78.PN
      DomainTheory.NeighbourhoodSystems.Example78.PN)
    DomainTheory.NeighbourhoodSystems.Example78.PN
    (@DomainTheory.NeighbourhoodSystems.funPresentation Nat Nat DomainTheory.NeighbourhoodSystems.Example78.PN
      DomainTheory.NeighbourhoodSystems.Example78.PN DomainTheory.NeighbourhoodSystems.Example78.PNpres
      DomainTheory.NeighbourhoodSystems.Example78.PNpres gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p hincl1 hincl1p heq1
      heq1p)
    DomainTheory.NeighbourhoodSystems.Example78.PNpres DomainTheory.NeighbourhoodSystems.Exercise723.graphMap :=
  DomainTheory.NeighbourhoodSystems.Exercise723.graphMap_isComputable

end DomainTheory.NeighbourhoodSystems.Exercise723
