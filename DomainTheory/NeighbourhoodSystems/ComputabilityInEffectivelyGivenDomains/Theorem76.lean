module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.fixMap_isComputable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_76.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V) (gN incl eq : Nat → Nat)
  (hgN :
    ∀ (c : Nat),
      Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.stepFun α α V V
            (@DomainTheory.NeighbourhoodSystems.funListOf α α V V P P (Domain.Recursive.decodeList c)))))
  (hgNp : Nat.Primrec gN)
  (hincl :
    ∀ (s : Nat),
      Iff (@Eq Nat (incl s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@LE.le (Set α) (@Set.instLE α)
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P (@Prod.fst Nat Nat (Nat.unpair s)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P (@Prod.snd Nat Nat (Nat.unpair s)))))
  (hinclp : Nat.Primrec incl)
  (heq :
    ∀ (s : Nat),
      Iff (@Eq Nat (eq s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq (Set α)
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P (@Prod.fst Nat Nat (Nat.unpair s)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P (@Prod.snd Nat Nat (Nat.unpair s)))))
  (heqp : Nat.Primrec eq),
  @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
    (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
    (@DomainTheory.NeighbourhoodSystems.funPresentation α α V V P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
      heq heqp)
    P (@DomainTheory.NeighbourhoodSystems.fixMap α V) :=
  @DomainTheory.NeighbourhoodSystems.fixMap_isComputable

end DomainTheory.NeighbourhoodSystems
