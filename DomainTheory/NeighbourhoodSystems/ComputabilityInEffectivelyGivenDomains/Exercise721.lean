/-ai
If evaluation is recursively enumerable on codes of computable presentations of the function space, the domain, and the codomain, then the relation of papplyEval on the corresponding power-domain codes is recursively enumerable. Over computable presentations of the function space, the domain, and the codomain, papplyEval relates the power-domain neighbourhoods coded by three natural numbers if and only if every code in the first decoded list and every code in the second admit a code in the third such that evaluation relates the three presented neighbourhoods. For neighbourhoods X₀ and Y₀, papplyEval relates the upset of the step neighbourhood of functions sending X₀ into Y₀, the upset of X₀, and the upset of Y₀.

The numbered name example_721 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval_rel_Ypd_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval_step_witness

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_721.{u_1, u_2} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (Pf :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W),
      (Domain.Recursive.REPred fun (s : Nat) =>
          @DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) α β
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) V W (@DomainTheory.NeighbourhoodSystems.eval α β V W)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P
              (@Prod.fst Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair s)))))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q
              (@Prod.snd Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair s)))))) →
        Domain.Recursive.REPred fun (w : Nat) =>
          @DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
            (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)) (Set α) (Set β)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
            (@DomainTheory.NeighbourhoodSystems.papplyEval α β V W)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf (@Prod.fst Nat Nat (Nat.unpair w)))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P
              (@Prod.fst Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair w)))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q
              (@Prod.snd Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair w))))))
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (Pf :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) {Φc Ac Bc : Nat},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
          (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)) (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.papplyEval α β V W)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf Φc)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P Ac)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q Bc))
        (∀ (g : Nat),
          @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList Φc) g →
            ∀ (x : Nat),
              @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList Ac) x →
                ∃ (y : Nat),
                  And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList Bc) y)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) α β
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) V W
                      (@DomainTheory.NeighbourhoodSystems.eval α β V W)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                        (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf g)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P x)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q y)))))
  (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {X₀ : Set α} {Y₀ : Set β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X₀ →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β W Y₀ →
        @DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
          (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)) (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.papplyEval α β V W)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
            (@DomainTheory.NeighbourhoodSystems.step α β V W X₀ Y₀))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet β W Y₀)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (Pf :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W),
      (Domain.Recursive.REPred fun (s : Nat) =>
          @DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) α β
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) V W (@DomainTheory.NeighbourhoodSystems.eval α β V W)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P
              (@Prod.fst Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair s)))))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q
              (@Prod.snd Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair s)))))) →
        Domain.Recursive.REPred fun (w : Nat) =>
          @DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
            (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)) (Set α) (Set β)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
            (@DomainTheory.NeighbourhoodSystems.papplyEval α β V W)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf (@Prod.fst Nat Nat (Nat.unpair w)))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P
              (@Prod.fst Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair w)))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q
              (@Prod.snd Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair w))))))
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (Pf :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) {Φc Ac Bc : Nat},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
          (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)) (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.papplyEval α β V W)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf Φc)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P Ac)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q Bc))
        (∀ (g : Nat),
          @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList Φc) g →
            ∀ (x : Nat),
              @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList Ac) x →
                ∃ (y : Nat),
                  And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList Bc) y)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) α β
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) V W
                      (@DomainTheory.NeighbourhoodSystems.eval α β V W)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                        (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf g)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P x)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q y)))))
  (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {X₀ : Set α} {Y₀ : Set β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X₀ →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β W Y₀ →
        @DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
          (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)) (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.papplyEval α β V W)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
            (@DomainTheory.NeighbourhoodSystems.step α β V W X₀ Y₀))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet β W Y₀))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (Pf :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W),
      (Domain.Recursive.REPred fun (s : Nat) =>
          @DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) α β
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) V W (@DomainTheory.NeighbourhoodSystems.eval α β V W)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P
              (@Prod.fst Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair s)))))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q
              (@Prod.snd Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair s)))))) →
        Domain.Recursive.REPred fun (w : Nat) =>
          @DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
            (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)) (Set α) (Set β)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
            (@DomainTheory.NeighbourhoodSystems.papplyEval α β V W)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf (@Prod.fst Nat Nat (Nat.unpair w)))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P
              (@Prod.fst Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair w)))))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q
              (@Prod.snd Nat Nat (Nat.unpair (@Prod.snd Nat Nat (Nat.unpair w))))))
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (Pf :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) {Φc Ac Bc : Nat},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
          (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)) (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.papplyEval α β V W)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf Φc)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P Ac)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q Bc))
        (∀ (g : Nat),
          @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList Φc) g →
            ∀ (x : Nat),
              @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList Ac) x →
                ∃ (y : Nat),
                  And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList Bc) y)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.rel
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) α β
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) V W
                      (@DomainTheory.NeighbourhoodSystems.eval α β V W)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                        (@DomainTheory.NeighbourhoodSystems.funSpace α β V W) Pf g)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P x)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q y))))
    @DomainTheory.NeighbourhoodSystems.papplyEval_isComputable
    @DomainTheory.NeighbourhoodSystems.papplyEval_rel_Ypd_iff)
  @DomainTheory.NeighbourhoodSystems.papplyEval_step_witness

end DomainTheory.NeighbourhoodSystems
