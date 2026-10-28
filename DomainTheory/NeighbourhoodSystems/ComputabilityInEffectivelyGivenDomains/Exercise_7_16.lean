module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table_5_5

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_12

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

theorem curryComb_rel_recDecidable
    (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (P₂ : ComputablePresentation V₂) (gNa gNb gNc : ℕ → ℕ)
    (PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂))
    (PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂)))
    (Pc : ComputablePresentation (funSpace V₁ V₂))
    (hPAX : PA.X = Xenum (prodPresentation P₀ P₁) P₂ gNa)
    (hPBX : PB.X = Xenum P₀ Pc gNb)
    (hPcX : Pc.X = Xenum P₁ P₂ gNc)
    (hgNa : ∀ c, gNa c = 1 ↔
      (stepFun (funListOf (prodPresentation P₀ P₁) P₂ (decodeList c))
        : Set (ApproximableMap (prod V₀ V₁) V₂)).Nonempty)
    (hgNc : ∀ c, gNc c = 1 ↔
      (stepFun (funListOf P₁ P₂ (decodeList c)) : Set (ApproximableMap V₁ V₂)).Nonempty)
    (hgNbp : Nat.Primrec gNb) (hgNcp : Nat.Primrec gNc) :
    RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m)) := by

  have hcomb : ∀ n m, (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m) ↔
      (gNb m = 1 → ∀ e ∈ decodeList m, gNc e.unpair.2 = 1 →
        ∀ e' ∈ decodeList e.unpair.2, PA.X n ⊆ PA.X (curryStepCode e.unpair.1 e')) := by
    intro n m
    have hstep1 : (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m) ↔
        curry (toApproxMap ((funSpace (prod V₀ V₁) V₂).principal (PA.mem_X n))) ∈ PB.X m := by
      constructor
      · rintro ⟨hG, hH⟩
        rw [curryIso_apply, mem_toFilter] at hH
        exact hH.2
      · intro h
        exact ⟨PA.mem_X n, by rw [curryIso_apply, mem_toFilter]; exact ⟨PB.mem_X m, h⟩⟩
    rw [hstep1, hPBX, mem_Xenum_iff_map P₀ Pc gNb
      (curry (toApproxMap ((funSpace (prod V₀ V₁) V₂).principal (PA.mem_X n)))) m]
    apply imp_congr_right; intro _
    apply forall_congr'; intro e
    apply imp_congr_right; intro _
    rw [hPcX, curry_rel_Xenum_iff P₀ P₁ P₂ gNc hgNc
      (toApproxMap ((funSpace (prod V₀ V₁) V₂).principal (PA.mem_X n))) e.unpair.1 e.unpair.2]
    apply imp_congr_right; intro _
    apply forall_congr'; intro e'
    apply imp_congr_right; intro _
    have hstepeq : step (prodNbhd (P₀.X e.unpair.1) (P₁.X e'.unpair.1)) (P₂.X e'.unpair.2)
        = PA.X (curryStepCode e.unpair.1 e') := by
      have hs := Xenum_singleton (prodPresentation P₀ P₁) P₂ gNa hgNa
        (Nat.pair e.unpair.1 e'.unpair.1) e'.unpair.2
      rw [prodPresentation_X, unpair_pair_fst, unpair_pair_snd] at hs
      rw [hPAX]; exact hs.symm
    rw [toApproxMap_rel, mem_principal, hstepeq]
    exact ⟨fun h => h.2, fun h => ⟨PA.mem_X _, h⟩⟩

  have q1_dec : RecDecidable₂ (fun e' p =>
      PA.X p.unpair.1 ⊆ PA.X (curryStepCode p.unpair.2 e')) := by
    have hr : Nat.Primrec (fun w => Nat.pair w.unpair.2.unpair.1
        (curryStepCode w.unpair.2.unpair.2 w.unpair.1)) :=
      (Nat.Primrec.left.comp Nat.Primrec.right).pair
        (primrec_curryStepCode (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left)
    refine RecDecidable.of_iff (fun w => ?_) (RecDecidable.comp PA.incl_computable hr)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have dInner := q1_dec.bForallList
  have dMid : RecDecidable₂ (fun e n =>
      gNc e.unpair.2 = 1 → ∀ e' ∈ decodeList e.unpair.2,
        PA.X n ⊆ PA.X (curryStepCode e.unpair.1 e')) := by
    have hg_mid : Nat.Primrec (fun s => Nat.pair s.unpair.1.unpair.2
        (Nat.pair s.unpair.2 s.unpair.1.unpair.1)) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.pair (Nat.Primrec.left.comp Nat.Primrec.left))
    have B1 : RecDecidable (fun s => ∀ e' ∈ decodeList s.unpair.1.unpair.2,
        PA.X s.unpair.2 ⊆ PA.X (curryStepCode s.unpair.1.unpair.1 e')) := by
      refine RecDecidable.of_iff (fun s => ?_) (RecDecidable.comp dInner hg_mid)
      simp only [unpair_pair_fst, unpair_pair_snd]
    have guard1 : RecDecidable (fun s => gNc s.unpair.1.unpair.2 = 1) :=
      RecDecidable.natEq (hgNcp.comp (Nat.Primrec.right.comp Nat.Primrec.left))
        (Nat.Primrec.const 1)
    refine RecDecidable.of_iff (fun s => ?_) (guard1.not.or B1)
    exact Decidable.imp_iff_not_or
  have dOuter := dMid.bForallList
  refine RecDecidable.of_iff (fun t => hcomb t.unpair.1 t.unpair.2) ?_
  have hswap2 : Nat.Primrec (fun t => Nat.pair t.unpair.2 t.unpair.1) :=
    Nat.Primrec.right.pair Nat.Primrec.left
  have B2 : RecDecidable (fun t => ∀ e ∈ decodeList t.unpair.2, gNc e.unpair.2 = 1 →
      ∀ e' ∈ decodeList e.unpair.2, PA.X t.unpair.1 ⊆ PA.X (curryStepCode e.unpair.1 e')) := by
    refine RecDecidable.of_iff (fun t => ?_) (RecDecidable.comp dOuter hswap2)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have guard2 : RecDecidable (fun t => gNb t.unpair.2 = 1) :=
    RecDecidable.natEq (hgNbp.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  refine RecDecidable.of_iff (fun t => ?_) (guard2.not.or B2)
  exact Decidable.imp_iff_not_or

theorem curryComb_isComputable
    (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (P₂ : ComputablePresentation V₂) :
    ∃ (PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂))
      (PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂))),
      RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m)) ∧
        ComputableMap PA PB (curryC V₀ V₁ V₂) := by
  obtain ⟨incl0, hincl0p, hincl0s⟩ := P₀.incl_computable
  obtain ⟨fc0, hfc0p, hfc0s⟩ := P₀.cons_computable
  obtain ⟨incl1, hincl1p, hincl1s⟩ := P₁.incl_computable
  obtain ⟨fc1, hfc1p, hfc1s⟩ := P₁.cons_computable
  obtain ⟨incl2, hincl2p, hincl2s⟩ := P₂.incl_computable
  obtain ⟨eq2, heq2p, heq2s⟩ := P₂.eq_computable
  obtain ⟨fc2, hfc2p, hfc2s⟩ := P₂.cons_computable
  obtain ⟨inclpr, hinclprp, hinclprs⟩ := (prodPresentation P₀ P₁).incl_computable
  obtain ⟨fcpr, hfcprp, hfcprs⟩ := (prodPresentation P₀ P₁).cons_computable

  let Pc : ComputablePresentation (funSpace V₁ V₂) :=
    funPresentation P₁ P₂ (funConsChar P₁ P₂ fc1 fc2) incl1 incl2 eq2
      (funConsChar_spec P₁ P₂ fc1 fc2 (fun s => (hfc1s s).symm) (fun s => (hfc2s s).symm))
      (primrec_funConsChar P₁ P₂ fc1 fc2 hfc1p hfc2p)
      (fun s => (hincl1s s).symm) hincl1p (fun s => (hincl2s s).symm) hincl2p
      (fun s => (heq2s s).symm) heq2p
  obtain ⟨inclc, hinclcp, hinclcs⟩ := Pc.incl_computable
  obtain ⟨eqc, heqcp, heqcs⟩ := Pc.eq_computable
  obtain ⟨fcc, hfccp, hfccs⟩ := Pc.cons_computable

  let PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂) :=
    funPresentation (prodPresentation P₀ P₁) P₂
      (funConsChar (prodPresentation P₀ P₁) P₂ fcpr fc2) inclpr incl2 eq2
      (funConsChar_spec (prodPresentation P₀ P₁) P₂ fcpr fc2
        (fun s => (hfcprs s).symm) (fun s => (hfc2s s).symm))
      (primrec_funConsChar (prodPresentation P₀ P₁) P₂ fcpr fc2 hfcprp hfc2p)
      (fun s => (hinclprs s).symm) hinclprp (fun s => (hincl2s s).symm) hincl2p
      (fun s => (heq2s s).symm) heq2p

  let PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂)) :=
    funPresentation P₀ Pc (funConsChar P₀ Pc fc0 fcc) incl0 inclc eqc
      (funConsChar_spec P₀ Pc fc0 fcc (fun s => (hfc0s s).symm) (fun s => (hfccs s).symm))
      (primrec_funConsChar P₀ Pc fc0 fcc hfc0p hfccp)
      (fun s => (hincl0s s).symm) hincl0p (fun s => (hinclcs s).symm) hinclcp
      (fun s => (heqcs s).symm) heqcp
  have hRec : RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m)) :=
    curryComb_rel_recDecidable P₀ P₁ P₂
      (funConsChar (prodPresentation P₀ P₁) P₂ fcpr fc2) (funConsChar P₀ Pc fc0 fcc)
      (funConsChar P₁ P₂ fc1 fc2) PA PB Pc rfl rfl rfl
      (funConsChar_spec (prodPresentation P₀ P₁) P₂ fcpr fc2
        (fun s => (hfcprs s).symm) (fun s => (hfc2s s).symm))
      (funConsChar_spec P₁ P₂ fc1 fc2 (fun s => (hfc1s s).symm) (fun s => (hfc2s s).symm))
      (primrec_funConsChar P₀ Pc fc0 fcc hfc0p hfccp)
      (primrec_funConsChar P₁ P₂ fc1 fc2 hfc1p hfc2p)
  exact ⟨PA, PB, hRec, ⟨hRec.re⟩⟩

theorem toApproxMap_principal_mem {G : Set (ApproximableMap V₀ V₁)}
    (hG : (funSpace V₀ V₁).mem G) : toApproxMap ((funSpace V₀ V₁).principal hG) ∈ G := by
  obtain ⟨L, hL, rfl⟩ := hG.1
  intro p hp
  show (toApproxMap ((funSpace V₀ V₁).principal hG)).rel p.1 p.2
  rw [toApproxMap_rel, mem_principal]
  exact ⟨step_mem (hL p hp).1 (hL p hp).2, fun f hf => hf p hp⟩

theorem curryComb_rel {G : Set (ApproximableMap (prod V₀ V₁) V₂)}
    {H : Set (ApproximableMap V₀ (funSpace V₁ V₂))} :
    (curryC V₀ V₁ V₂).rel G H ↔ (funSpace (prod V₀ V₁) V₂).mem G ∧
      (funSpace V₀ (funSpace V₁ V₂)).mem H ∧ ∀ g ∈ G, curry g ∈ H := by
  constructor
  · rintro ⟨hG, hH⟩
    rw [curryIso_apply, mem_toFilter] at hH
    obtain ⟨hHmem, hcurry⟩ := hH
    refine ⟨hG, hHmem, fun g hg => ?_⟩
    have hle : toApproxMap ((funSpace (prod V₀ V₁) V₂).principal hG) ≤ g := by
      rw [ApproximableMap.le_iff]
      intro X Y hrel
      rw [toApproxMap_rel, mem_principal] at hrel
      exact hrel.2 hg
    have hcle : curry (toApproxMap ((funSpace (prod V₀ V₁) V₂).principal hG)) ≤ curry g :=
      (curryEquiv V₀ V₁ V₂).monotone hle
    exact funSpace_mem_up_closed hHmem hcurry hcle
  · rintro ⟨hG, hH, hall⟩
    refine ⟨hG, ?_⟩
    rw [curryIso_apply, mem_toFilter]
    exact ⟨hH, hall _ (toApproxMap_principal_mem hG)⟩

end

section
set_option linter.unusedVariables false

theorem example_716.{u_1, u_2, u_3} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
      (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂),
      ∃ (PA :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂))
        (PB :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))),
        And
          (Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                PA n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                (@DomainTheory.NeighbourhoodSystems.funSpace α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                PB m))
          (@DomainTheory.NeighbourhoodSystems.ComputableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PA PB (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {G :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)}
      {H :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂) G H)
        (And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            G)
          (And
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              H)
            (∀
              (g :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂),
              @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  G g →
                @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  H (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g))))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
    (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gNa gNb gNc : Nat → Nat)
    (PA :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          V₂))
    (PB :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
    (Pc :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)),
    @Eq
        (Nat →
          Set
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          PA)
        (@DomainTheory.NeighbourhoodSystems.Xenum (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
          (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ gNa) →
      @Eq
          (Nat →
            Set
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PB)
          (@DomainTheory.NeighbourhoodSystems.Xenum α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀ Pc gNb) →
        @Eq (Nat → Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) Pc)
            (@DomainTheory.NeighbourhoodSystems.Xenum β γ V₁ V₂ P₁ P₂ gNc) →
          (∀ (c : Nat),
              Iff (@Eq Nat (gNa c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Set.Nonempty
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (@DomainTheory.NeighbourhoodSystems.stepFun (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
                    (@DomainTheory.NeighbourhoodSystems.funListOf (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
                      (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂
                      (Domain.Recursive.decodeList c))))) →
            (∀ (c : Nat),
                Iff (@Eq Nat (gNc c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                    (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                      (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂
                        (Domain.Recursive.decodeList c))))) →
              Nat.Primrec gNb →
                Nat.Primrec gNc →
                  Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                      (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                      (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                        (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                        PA n)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                        (@DomainTheory.NeighbourhoodSystems.funSpace α
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                        PB m)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
      (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂),
      ∃ (PA :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂))
        (PB :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))),
        And
          (Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                PA n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                (@DomainTheory.NeighbourhoodSystems.funSpace α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                PB m))
          (@DomainTheory.NeighbourhoodSystems.ComputableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PA PB (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {G :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)}
      {H :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂) G H)
        (And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            G)
          (And
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              H)
            (∀
              (g :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂),
              @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  G g →
                @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  H (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g))))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
    (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gNa gNb gNc : Nat → Nat)
    (PA :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          V₂))
    (PB :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
        (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
    (Pc :
      @DomainTheory.NeighbourhoodSystems.ComputablePresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)),
    @Eq
        (Nat →
          Set
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
        (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          PA)
        (@DomainTheory.NeighbourhoodSystems.Xenum (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
          (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ gNa) →
      @Eq
          (Nat →
            Set
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PB)
          (@DomainTheory.NeighbourhoodSystems.Xenum α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀ Pc gNb) →
        @Eq (Nat → Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) Pc)
            (@DomainTheory.NeighbourhoodSystems.Xenum β γ V₁ V₂ P₁ P₂ gNc) →
          (∀ (c : Nat),
              Iff (@Eq Nat (gNa c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Set.Nonempty
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (@DomainTheory.NeighbourhoodSystems.stepFun (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
                    (@DomainTheory.NeighbourhoodSystems.funListOf (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
                      (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂
                      (Domain.Recursive.decodeList c))))) →
            (∀ (c : Nat),
                Iff (@Eq Nat (gNc c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                    (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                      (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂
                        (Domain.Recursive.decodeList c))))) →
              Nat.Primrec gNb →
                Nat.Primrec gNc →
                  Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                      (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                      (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                        (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                        PA n)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                        (@DomainTheory.NeighbourhoodSystems.funSpace α
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                          (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                        PB m))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
      (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂),
      ∃ (PA :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂))
        (PB :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))),
        And
          (Domain.Recursive.RecDecidable₂ fun (n m : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                PA n)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                (@DomainTheory.NeighbourhoodSystems.funSpace α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                PB m))
          (@DomainTheory.NeighbourhoodSystems.ComputableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
            PA PB (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂)))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      {G :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)}
      {H :
        Set
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            V₂)
          (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
          (@DomainTheory.NeighbourhoodSystems.curryC α β γ V₀ V₁ V₂) G H)
        (And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              V₂)
            G)
          (And
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              (@DomainTheory.NeighbourhoodSystems.funSpace α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
              H)
            (∀
              (g :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂),
              @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                    (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
                      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
                  G g →
                @Membership.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
                  (Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  (@Set.instMembership
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)))
                  H (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)))))
    @DomainTheory.NeighbourhoodSystems.curryComb_isComputable @DomainTheory.NeighbourhoodSystems.curryComb_rel)
  @DomainTheory.NeighbourhoodSystems.curryComb_rel_recDecidable
end

end DomainTheory.NeighbourhoodSystems
end
