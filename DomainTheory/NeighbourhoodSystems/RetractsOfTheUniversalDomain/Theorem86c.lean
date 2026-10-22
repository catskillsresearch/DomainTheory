module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.subApprox_isComputable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.sub_isComputable_of_isEffectivelyGiven

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_86_c.{u_1} : And
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E) (gN : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.stepFun α α E E
              (@DomainTheory.NeighbourhoodSystems.funListOf α α E E P P (Domain.Recursive.decodeList c)))))
    (incl eq : Nat → Nat) (hgNp : Nat.Primrec gN)
    (hincl :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hinclp : Nat.Primrec incl)
    (heq :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heqp : Nat.Primrec eq),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α E →
      ∃ (Pfun :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
        @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
          Pfun Pfun (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E)) :=
  @And.intro
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E) (gN : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.stepFun α α E E
              (@DomainTheory.NeighbourhoodSystems.funListOf α α E E P P (Domain.Recursive.decodeList c)))))
    (incl eq : Nat → Nat) (hgNp : Nat.Primrec gN)
    (hincl :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hinclp : Nat.Primrec incl)
    (heq :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heqp : Nat.Primrec eq),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α E →
      ∃ (Pfun :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
        @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
          Pfun Pfun (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
  @DomainTheory.NeighbourhoodSystems.subApprox_isComputable
  @DomainTheory.NeighbourhoodSystems.sub_isComputable_of_isEffectivelyGiven

end DomainTheory.NeighbourhoodSystems
