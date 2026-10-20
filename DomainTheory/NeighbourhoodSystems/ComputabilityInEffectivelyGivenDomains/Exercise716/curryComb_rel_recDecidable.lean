module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.curryIso_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.primrec_curryStepCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}





/-- **Exercise 7.16 — `curry` is a *recursive* set.** Relative to the function-space presentations
`PA` of `(𝒟₀×𝒟₁→𝒟₂)` and `PB` of `(𝒟₀→(𝒟₁→𝒟₂))` (and the inner one `Pc` of `(𝒟₁→𝒟₂)`) built by
Theorem 7.5, the `curry` combinator's neighbourhood relation is **recursively decidable**:

  `Xenum_PA n curryComb Xenum_PB m  ⟺  gNb m = 1 → ∀ e ∈ ⟦m⟧, gNc e₂ = 1 →
                                          ∀ e' ∈ ⟦e₂⟧, X_PA n ⊆ X_PA (curryStepCode e₁ e')`,

a bounded double-`∀` over the coded entry-lists of the recursively *decidable* function-space
inclusion. So `curry` is a recursive set — exactly as for `eval`. -/
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
  -- The explicit neighbourhood relation, written out over the coded entries.
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
  -- The right-hand side is recursively decidable.
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

end DomainTheory.NeighbourhoodSystems
