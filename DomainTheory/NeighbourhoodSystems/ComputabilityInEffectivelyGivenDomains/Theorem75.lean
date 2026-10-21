/-ai
An element of the function space has a recursively enumerable set of enumeration indices if and only if the corresponding approximable map is computable. Scott's Theorem 7.5 says that if two domains are effectively given then so is their function space, that evaluation and currying are computable, and that the computable elements are exactly the computable maps. If a map out of a product is computable, its currying into the function space is computable. Evaluation from the product of the function space with the domain into the codomain is computable. An element of the function-space presentation is a computable element if and only if the approximable map it determines is a computable map of the two component presentations.

The numbered name theorem_75 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_isComputableElement_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.curry_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.evalMap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.isComputableElement_funPresentation_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_75.{u_1, u_2, u_3} : And
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.IsComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gN incl0 incl1 eq1 : Nat → Nat)
        (hgN :
          ∀ (c : Nat),
            Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                  (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂ (Domain.Recursive.decodeList c)))))
        (hgNp : Nat.Primrec gN)
        (hincl0 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set β) (@Set.instLE β)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl0p : Nat.Primrec incl0)
        (hincl1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set γ) (@Set.instLE γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl1p : Nat.Primrec incl1)
        (heq1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq (Set γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (heq1p : Nat.Primrec eq1)
        {g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂},
        @DomainTheory.NeighbourhoodSystems.IsComputableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
            (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ g →
          @DomainTheory.NeighbourhoodSystems.IsComputableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀
            (@DomainTheory.NeighbourhoodSystems.funPresentation β γ V₁ V₂ P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0
              hincl0p hincl1 hincl1p heq1 heq1p)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
      (hgN :
        ∀ (c : Nat),
          Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
      (hgNp : Nat.Primrec gN)
      (hincl0 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set α) (@Set.instLE α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl0p : Nat.Primrec incl0)
      (hincl1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set β) (@Set.instLE β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl1p : Nat.Primrec incl1)
      (heq1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (heq1p : Nat.Primrec eq1),
      @DomainTheory.NeighbourhoodSystems.IsComputableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β
        (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
        V₁
        (@DomainTheory.NeighbourhoodSystems.prodPresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀
          (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
            hincl1 hincl1p heq1 heq1p)
          P₀)
        P₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
    (hgNp : Nat.Primrec gN)
    (hincl0 :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hincl0p : Nat.Primrec incl0)
    (hincl1 :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set β) (@Set.instLE β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hincl1p : Nat.Primrec incl1)
    (heq1 :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heq1p : Nat.Primrec eq1)
    (φ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    Iff
      (@DomainTheory.NeighbourhoodSystems.IsComputableElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
          hincl1 hincl1p heq1 heq1p)
        φ)
      (@DomainTheory.NeighbourhoodSystems.IsComputableMap α β V₀ V₁ P₀ P₁
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ))) :=
  @And.intro
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.IsComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gN incl0 incl1 eq1 : Nat → Nat)
        (hgN :
          ∀ (c : Nat),
            Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                  (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂ (Domain.Recursive.decodeList c)))))
        (hgNp : Nat.Primrec gN)
        (hincl0 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set β) (@Set.instLE β)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl0p : Nat.Primrec incl0)
        (hincl1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set γ) (@Set.instLE γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl1p : Nat.Primrec incl1)
        (heq1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq (Set γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (heq1p : Nat.Primrec eq1)
        {g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂},
        @DomainTheory.NeighbourhoodSystems.IsComputableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
            (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ g →
          @DomainTheory.NeighbourhoodSystems.IsComputableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀
            (@DomainTheory.NeighbourhoodSystems.funPresentation β γ V₁ V₂ P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0
              hincl0p hincl1 hincl1p heq1 heq1p)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
      (hgN :
        ∀ (c : Nat),
          Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
      (hgNp : Nat.Primrec gN)
      (hincl0 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set α) (@Set.instLE α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl0p : Nat.Primrec incl0)
      (hincl1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set β) (@Set.instLE β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl1p : Nat.Primrec incl1)
      (heq1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (heq1p : Nat.Primrec eq1),
      @DomainTheory.NeighbourhoodSystems.IsComputableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β
        (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
        V₁
        (@DomainTheory.NeighbourhoodSystems.prodPresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀
          (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
            hincl1 hincl1p heq1 heq1p)
          P₀)
        P₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
    (hgNp : Nat.Primrec gN)
    (hincl0 :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hincl0p : Nat.Primrec incl0)
    (hincl1 :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set β) (@Set.instLE β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hincl1p : Nat.Primrec incl1)
    (heq1 :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heq1p : Nat.Primrec eq1)
    (φ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    Iff
      (@DomainTheory.NeighbourhoodSystems.IsComputableElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
          hincl1 hincl1p heq1 heq1p)
        φ)
      (@DomainTheory.NeighbourhoodSystems.IsComputableMap α β V₀ V₁ P₀ P₁
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
  (@And.intro
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.IsComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gN incl0 incl1 eq1 : Nat → Nat)
        (hgN :
          ∀ (c : Nat),
            Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                  (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂ (Domain.Recursive.decodeList c)))))
        (hgNp : Nat.Primrec gN)
        (hincl0 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set β) (@Set.instLE β)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl0p : Nat.Primrec incl0)
        (hincl1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set γ) (@Set.instLE γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl1p : Nat.Primrec incl1)
        (heq1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq (Set γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (heq1p : Nat.Primrec eq1)
        {g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂},
        @DomainTheory.NeighbourhoodSystems.IsComputableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
            (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ g →
          @DomainTheory.NeighbourhoodSystems.IsComputableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀
            (@DomainTheory.NeighbourhoodSystems.funPresentation β γ V₁ V₂ P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0
              hincl0p hincl1 hincl1p heq1 heq1p)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
      (hgN :
        ∀ (c : Nat),
          Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
      (hgNp : Nat.Primrec gN)
      (hincl0 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set α) (@Set.instLE α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl0p : Nat.Primrec incl0)
      (hincl1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set β) (@Set.instLE β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl1p : Nat.Primrec incl1)
      (heq1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (heq1p : Nat.Primrec eq1),
      @DomainTheory.NeighbourhoodSystems.IsComputableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β
        (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
        V₁
        (@DomainTheory.NeighbourhoodSystems.prodPresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀
          (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
            hincl1 hincl1p heq1 heq1p)
          P₀)
        P₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁))
    (@And.intro
      (And
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.IsComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gN incl0 incl1 eq1 : Nat → Nat)
        (hgN :
          ∀ (c : Nat),
            Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                  (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂ (Domain.Recursive.decodeList c)))))
        (hgNp : Nat.Primrec gN)
        (hincl0 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set β) (@Set.instLE β)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl0p : Nat.Primrec incl0)
        (hincl1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set γ) (@Set.instLE γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl1p : Nat.Primrec incl1)
        (heq1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq (Set γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (heq1p : Nat.Primrec eq1)
        {g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂},
        @DomainTheory.NeighbourhoodSystems.IsComputableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
            (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ g →
          @DomainTheory.NeighbourhoodSystems.IsComputableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀
            (@DomainTheory.NeighbourhoodSystems.funPresentation β γ V₁ V₂ P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0
              hincl0p hincl1 hincl1p heq1 heq1p)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g))
      (@And.intro
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.IsComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
        @DomainTheory.NeighbourhoodSystems.Xenum_isComputableElement_iff
        @DomainTheory.NeighbourhoodSystems.funSpace_isEffectivelyGiven)
      @DomainTheory.NeighbourhoodSystems.curry_isComputable)
    @DomainTheory.NeighbourhoodSystems.evalMap_isComputable)
  @DomainTheory.NeighbourhoodSystems.isComputableElement_funPresentation_iff

end DomainTheory.NeighbourhoodSystems
