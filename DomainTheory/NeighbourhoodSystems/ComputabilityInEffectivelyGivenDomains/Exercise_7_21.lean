module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_19
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_11
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_10
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example_6_1
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem_6_9

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}
/- concordance: source L4689 EXERCISE 7.21 distributing the power domain -/
/-- **Exercise 7.21 — the two-variable combinator `papplyEval : ℙ(D→E) × ℙD → ℙE`.** The Smyth
power-domain lift of evaluation (Theorem 3.11): a `ℙ(D→E)`-neighbourhood `Φ` applied to a
`ℙD`-neighbourhood `A` covers a `ℙE`-neighbourhood `B` iff every function-neighbourhood `G ∈ Φ`
applied to every argument-neighbourhood `X ∈ A` lands in some `Y ∈ B` (via `eval`, i.e. every
`f ∈ G` sends `X` into `Y`). This is the two-variable analogue of Exercise 7.19's `ℙf`. -/
def papplyEval (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap₂ (funSpace V W).PowerDomain V.PowerDomain W.PowerDomain where
  rel Φ A B := (funSpace V W).PDmem Φ ∧ V.PDmem A ∧ W.PDmem B ∧
    ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, (eval V W).rel G X Y
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := by
    refine ⟨(funSpace V W).PDmem_master, V.PDmem_master, W.PDmem_master, ?_⟩
    intro G hG X hX
    simp only [mem_upSet] at hG hX
    refine ⟨W.master, ⟨W.master_mem, subset_rfl⟩, ?_⟩
    exact ⟨hG.1, hX.1, W.master_mem,
      fun f hf => f.mono f.master_rel (V.sub_master hX.1) subset_rfl hX.1 W.master_mem⟩
  inter_right := by
    rintro Φ A B B' ⟨hΦ, hA, hB, hbody⟩ ⟨-, -, hB', hbody'⟩
    refine ⟨hΦ, hA, W.PDmem_inter hB hB', ?_⟩
    intro G hG X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody G hG X hX
    obtain ⟨Y', hY'B', hrel'⟩ := hbody' G hG X hX
    have hinmem : W.mem (Y ∩ Y') := (eval V W).rel_cod ((eval V W).inter_right hrel hrel')
    exact ⟨Y ∩ Y', Set.mem_inter
      (W.PDmem_down hB hYB Set.inter_subset_left hinmem)
      (W.PDmem_down hB' hY'B' Set.inter_subset_right hinmem),
      (eval V W).inter_right hrel hrel'⟩
  mono := by
    rintro Φ Φ' A A' B B' ⟨_, _, _, hbody⟩ hΦ'Φ hA'A hBB' hΦ' hA' hB'
    refine ⟨hΦ', hA', hB', ?_⟩
    intro G hG X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody G (hΦ'Φ hG) X (hA'A hX)
    exact ⟨Y, hBB' hYB, hrel⟩
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}

@[simp] theorem papplyEval_rel {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {Φ : Set (Set (ApproximableMap V W))} {A : Set (Set α)} {B : Set (Set β)} :
    (papplyEval V W).rel Φ A B ↔ (funSpace V W).PDmem Φ ∧ V.PDmem A ∧ W.PDmem B ∧
      ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, (eval V W).rel G X Y := Iff.rfl
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}

/-- **Exercise 7.21 — the combinator as a map out of the product `ℙ(D→E) × ℙD → ℙE`.** -/
def papplyB (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V W).PowerDomain V.PowerDomain) W.PowerDomain :=
  ofMap₂ (papplyEval V W)
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}

/-- **Exercise 7.21 — the headline combinator `papply : ℙ(D→E) → (ℙD → ℙE)`.** Currying `papplyB`
(Theorem 3.12) gives the combinator of *exactly* the type Scott asks for. -/
def papply (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (funSpace V W).PowerDomain (funSpace V.PowerDomain W.PowerDomain) :=
  curry (papplyB V W)
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}

/-- **Exercise 7.21 — `papply`'s relation at the level of `ℙ𝒟`-codes.** Over the canonical
presentations of Proposition 7.10 (function-space presentation `Pf`, domain `P`, codomain `Q`):
`papplyEval.rel (Y_Φc) (Y_Ac) (Y_Bc) ↔ ∀ g ∈ dl Φc, ∀ x ∈ dl Ac, ∃ y ∈ dl Bc, eval (Pf.X g)(P.X x)(Q.X y)`. -/
theorem papplyEval_rel_Ypd_iff {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (Pf : ComputablePresentation (funSpace V W)) (P : ComputablePresentation V)
    (Q : ComputablePresentation W) {Φc Ac Bc : ℕ} :
    (papplyEval V W).rel ((funSpace V W).Ypd Pf Φc) (V.Ypd P Ac) (W.Ypd Q Bc)
      ↔ ∀ g ∈ decodeList Φc, ∀ x ∈ decodeList Ac, ∃ y ∈ decodeList Bc,
          (eval V W).rel (Pf.X g) (P.X x) (Q.X y) := by
  constructor
  · rintro ⟨-, -, -, hbody⟩ g hg x hx
    have hGin : Pf.X g ∈ (funSpace V W).Ypd Pf Φc :=
      ((funSpace V W).mem_Ypd Pf).mpr ⟨g, hg, Pf.mem_X g, subset_rfl⟩
    have hXin : P.X x ∈ V.Ypd P Ac := (V.mem_Ypd P).mpr ⟨x, hx, P.mem_X x, subset_rfl⟩
    obtain ⟨Y, hYin, hrel⟩ := hbody (Pf.X g) hGin (P.X x) hXin
    obtain ⟨b, hb, hYmem, hYsub⟩ := (W.mem_Ypd Q).mp hYin
    exact ⟨b, hb, (eval V W).mono hrel subset_rfl subset_rfl hYsub
      ((eval V W).rel_dom₀ hrel) ((eval V W).rel_dom₁ hrel) (Q.mem_X b)⟩
  · intro hgen
    refine ⟨(funSpace V W).Ypd_isPDmem Pf Φc, V.Ypd_isPDmem P Ac, W.Ypd_isPDmem Q Bc, ?_⟩
    intro G hGin X hXin
    obtain ⟨g, hg, hGmem, hGsub⟩ := ((funSpace V W).mem_Ypd Pf).mp hGin
    obtain ⟨x, hx, hXmem, hXsub⟩ := (V.mem_Ypd P).mp hXin
    obtain ⟨y, hy, hrel⟩ := hgen g hg x hx
    exact ⟨Q.X y, (W.mem_Ypd Q).mpr ⟨y, hy, Q.mem_X y, subset_rfl⟩,
      (eval V W).mono hrel hGsub hXsub subset_rfl hGmem hXmem (Q.mem_X y)⟩
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}

/-- **Exercise 7.21 — non-triviality.** For any neighbourhoods `X₀ ∈ D`, `Y₀ ∈ E`, the set of
functions sending `X₀` into `Y₀` (the principal `ℙ(D→E)`-element `↓[X₀,Y₀]`), applied to the
argument-set `↓X₀`, covers `↓Y₀`. So `papply` does genuine work (it is not the constant map). -/
theorem papplyEval_step_witness {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {X₀ : Set α} {Y₀ : Set β} (hX₀ : V.mem X₀) (hY₀ : W.mem Y₀) :
    (papplyEval V W).rel ((funSpace V W).upSet (step X₀ Y₀)) (V.upSet X₀) (W.upSet Y₀) := by
  refine ⟨(funSpace V W).PDmem_upSet (step_mem hX₀ hY₀), V.PDmem_upSet hX₀,
    W.PDmem_upSet hY₀, ?_⟩
  intro G hG X hX
  obtain ⟨hGmem, hGsub⟩ := hG
  obtain ⟨hXmem, hXsub⟩ := hX
  refine ⟨Y₀, ⟨hY₀, subset_rfl⟩, hGmem, hXmem, hY₀, ?_⟩
  intro f hf
  have hfstep : f.rel X₀ Y₀ := mem_step.mp (hGsub hf)
  exact f.mono hfstep hXsub subset_rfl hXmem hY₀
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}

/-- **Three nested bounded quantifiers preserve recursive enumerability.** If `R` is r.e. (in the
paired form `R g x y`) then so is `∀ g ∈ dl w.1, ∀ x ∈ dl w.2.1, ∃ y ∈ dl w.2.2, R g x y`. Built from
the bounded-`∃` lemma `bExists_decodeList_re` (Exercise 7.19) and the parameterised bounded-`∀` lemma
`REPred.forall_mem_decodeList₂`, layered with primitive-recursive re-indexings. -/
theorem re_forallG_forallX_existsY {R : ℕ → ℕ → ℕ → Prop}
    (hR : REPred (fun s => R s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2)) :
    REPred (fun w => ∀ g ∈ decodeList w.unpair.1, ∀ x ∈ decodeList w.unpair.2.unpair.1,
      ∃ y ∈ decodeList w.unpair.2.unpair.2, R g x y) := by
  -- reindex `⟨g,x,y⟩ = ⟨s.1.1, s.1.2, s.2⟩` ↦ `⟨g,⟨x,y⟩⟩`
  have hm1 : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.1.unpair.1
      (Nat.pair s.unpair.1.unpair.2 s.unpair.2)) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair
      ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
  have hR2 : REPred₂ (fun gx y => R gx.unpair.1 gx.unpair.2 y) := by
    show REPred (fun t => R t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2)
    refine REPred.of_iff (fun s => ?_) (hR.comp hm1)
    simp only [unpair_pair_fst, unpair_pair_snd]
  -- bounded `∃ y`
  have hE : REPred (fun u => ∃ b ∈ decodeList u.unpair.1,
      R u.unpair.2.unpair.1 u.unpair.2.unpair.2 b) := bExists_decodeList_re hR2
  -- bounded `∀ x` (parameters `⟨Bc, g⟩`)
  have hm2 : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1
      (Nat.pair t.unpair.1.unpair.2 t.unpair.2)) := hm1
  have hF : REPred₂ (fun param x => ∃ y ∈ decodeList param.unpair.1,
      R param.unpair.2 x y) := by
    show REPred (fun t => ∃ y ∈ decodeList t.unpair.1.unpair.1,
      R t.unpair.1.unpair.2 t.unpair.2 y)
    refine REPred.of_iff (fun t => ?_) (hE.comp hm2)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hFfull : REPred (fun t => ∀ x ∈ decodeList t.unpair.2,
      ∃ y ∈ decodeList t.unpair.1.unpair.1, R t.unpair.1.unpair.2 x y) :=
    REPred.forall_mem_decodeList₂ hF
  -- bounded `∀ g` (parameters `⟨Bc, Ac⟩`)
  have hm3 : Nat.Primrec (fun t : ℕ => Nat.pair
      (Nat.pair t.unpair.1.unpair.1 t.unpair.2) t.unpair.1.unpair.2) :=
    ((Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.left)
  have hG : REPred₂ (fun param g => ∀ x ∈ decodeList param.unpair.2,
      ∃ y ∈ decodeList param.unpair.1, R g x y) := by
    show REPred (fun t => ∀ x ∈ decodeList t.unpair.1.unpair.2,
      ∃ y ∈ decodeList t.unpair.1.unpair.1, R t.unpair.2 x y)
    refine REPred.of_iff (fun t => ?_) (hFfull.comp hm3)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hGfull : REPred (fun t => ∀ g ∈ decodeList t.unpair.2,
      ∀ x ∈ decodeList t.unpair.1.unpair.2,
        ∃ y ∈ decodeList t.unpair.1.unpair.1, R g x y) :=
    REPred.forall_mem_decodeList₂ hG
  -- final reindex to `w = ⟨Φc, ⟨Ac, Bc⟩⟩`
  have hm4 : Nat.Primrec (fun w : ℕ => Nat.pair
      (Nat.pair w.unpair.2.unpair.2 w.unpair.2.unpair.1) w.unpair.1) :=
    ((Nat.Primrec.right.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.comp Nat.Primrec.right)).pair Nat.Primrec.left
  refine REPred.of_iff (fun w => ?_) (hGfull.comp hm4)
  simp only [unpair_pair_fst, unpair_pair_snd]
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}

/-- **Exercise 7.21 (the computability half) — `papply` is computable when `eval` is.** Stated at the
level of the `ℙ𝒟`-codes of Proposition 7.10: given that `eval` is recursively enumerable on codes
(`heval` — this is Theorem 7.5's `evalMap_isComputable` transported through `funPresentation`), the
relation `papplyEval.rel (Y_Φc)(Y_Ac)(Y_Bc)` is recursively enumerable in `⟨Φc, Ac, Bc⟩`. -/
theorem papplyEval_isComputable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (Pf : ComputablePresentation (funSpace V W)) (P : ComputablePresentation V)
    (Q : ComputablePresentation W)
    (heval : REPred (fun s => (eval V W).rel (Pf.X s.unpair.1)
      (P.X s.unpair.2.unpair.1) (Q.X s.unpair.2.unpair.2))) :
    REPred (fun w => (papplyEval V W).rel ((funSpace V W).Ypd Pf w.unpair.1)
      (V.Ypd P w.unpair.2.unpair.1) (W.Ypd Q w.unpair.2.unpair.2)) := by
  refine REPred.of_iff (fun w => ?_)
    (re_forallG_forallX_existsY
      (R := fun g x y => (eval V W).rel (Pf.X g) (P.X x) (Q.X y)) heval)
  exact papplyEval_rel_Ypd_iff Pf P Q
end

section
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
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Consistency bit of a packed triple. -/
def consB (r : ℕ) : ℕ := r.unpair.2.unpair.1

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Equality bit of a packed triple. -/
def eqB (r : ℕ) : ℕ := r.unpair.1

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Intersection index of a packed triple. -/
def intI (r : ℕ) : ℕ := r.unpair.2.unpair.2

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

/-- `a ≤ Nat.pair a b` (choice-free). -/
theorem le_pair_left (a b : ℕ) : a ≤ Nat.pair a b := by
  unfold Nat.pair; split <;> omega

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- One step of the list-indexing fold: state `pair countdown value`; capture the current element
when `countdown = 1`, else carry the value and decrement. -/
def listGetStp (t : ℕ) : ℕ :=
  Nat.pair (t.unpair.2.unpair.1.unpair.1 - 1)
    (selectFn (isOne t.unpair.2.unpair.1.unpair.1) t.unpair.1 t.unpair.2.unpair.1.unpair.2)

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `listGet c i = (decodeList c).getD i 0`: the `i`-th entry of the list coded by `c`. -/
def listGet (c i : ℕ) : ℕ :=
  (foldCode listGetStp 0 (Nat.pair (i + 1) 0) c).unpair.2

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The fold step on an explicit accumulator `pair cd val`. -/
theorem listGetStp_pair (cd val x : ℕ) :
    listGetStp (Nat.pair x (Nat.pair (Nat.pair cd val) 0))
      = Nat.pair (cd - 1) (selectFn (isOne cd) x val) := by
  unfold listGetStp
  simp only [unpair_pair_fst, unpair_pair_snd]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- With `cd = 0` the fold is a fixed point on the value. -/
theorem listGet_foldl_zero (l : List ℕ) (val : ℕ) :
    (List.foldl (fun acc x => listGetStp (Nat.pair x (Nat.pair acc 0))) (Nat.pair 0 val) l).unpair.2
      = val := by
  induction l generalizing val with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, listGetStp_pair, Nat.zero_sub,
        show isOne 0 = 0 from rfl, selectFn_zero, ih]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The fold reads off the `cd-1`-th element (default `val`). -/
theorem listGet_foldl (l : List ℕ) (c val : ℕ) :
    (List.foldl (fun acc x => listGetStp (Nat.pair x (Nat.pair acc 0)))
        (Nat.pair (c + 1) val) l).unpair.2 = l.getD c val := by
  induction l generalizing c val with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, listGetStp_pair, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · rw [show isOne (0 + 1) = 1 from rfl, selectFn_one, listGet_foldl_zero,
          List.getD_cons_zero]
      · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        rw [show isOne (c' + 1 + 1) = 0 by unfold isOne; omega, selectFn_zero, ih,
          List.getD_cons_succ]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Correctness of `listGet`** on a coded list. -/
theorem listGet_encodeList (l : List ℕ) (i : ℕ) : listGet (encodeList l) i = l.getD i 0 := by
  unfold listGet
  rw [foldCode_eq]
  exact listGet_foldl l i 0

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

theorem max_sq_le_pair (i j : ℕ) : max i j * max i j ≤ Nat.pair i j := by
  unfold Nat.pair
  rcases lt_or_ge i j with h | h
  · rw [ite_eq_left h, show max i j = j by omega]; omega
  · rw [ite_eq_right (by omega), show max i j = i by omega]; omega

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem memS_sub_embPair (hD : ∀ X, D.mem X → X.Nonempty)
    {W A B : Set (List Bool × α)} (hW : MemS D W) (hsub : W ⊆ embPair A B) :
    ∃ Pp Qq, MemS D Pp ∧ MemS D Qq ∧ W = embPair Pp Qq := by
  cases hW with
  | gamma =>
      obtain ⟨a, ha⟩ := hD D.master D.master_mem
      rcases hsub (show (([], a) : List Bool × α) ∈ Gamma D from ha) with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp at hp'
      · simp at hq'
  | @zero Z hZ =>
      obtain ⟨a, ha⟩ := hD Z hZ
      rcases hsub (show (([], a) : List Bool × α) ∈ embZero Z from ⟨rfl, ha⟩) with
        ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp at hp'
      · simp at hq'
  | @pair Pp Qq hP hQ => exact ⟨Pp, Qq, hP, hQ, rfl⟩

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem memS_sub_embZero (hD : ∀ X, D.mem X → X.Nonempty) {W : Set (List Bool × α)} {Y : Set α}
    (hW : MemS D W) (hsub : W ⊆ embZero Y) : ∃ Z, D.mem Z ∧ W = embZero Z := by
  cases hW with
  | gamma =>
      obtain ⟨a, ha⟩ := hD D.master D.master_mem
      exact absurd (hsub (show ((true :: [], a) : List Bool × α) ∈ Gamma D from ha)).1 (by simp)
  | @zero Z hZ => exact ⟨Z, hZ, rfl⟩
  | @pair Pp Qq hP hQ =>
      obtain ⟨⟨pth, a⟩, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Qq)
      have hmem := hsub ht
      rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · exact absurd (hp'.symm.trans hmem.1) (by simp)
      · exact absurd (hq'.symm.trans hmem.1) (by simp)

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

/-- The three index shapes: `0` (master `Γ`), `2a+1` (leaf), `2a+2` (node). Choice-free. -/
theorem nat_shape (n : ℕ) : n = 0 ∨ (∃ a, n = 2 * a + 1) ∨ (∃ a, n = 2 * a + 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl rfl
  · rcases Nat.lt_or_ge (n % 2) 1 with h | h
    · exact Or.inr (Or.inr ⟨n / 2 - 1, by omega⟩)
    · exact Or.inr (Or.inl ⟨n / 2, by omega⟩)

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Pack the triple `(eqBit, consBit, interIdx)` into one natural. -/
def packT (e c ii : ℕ) : ℕ := Nat.pair e (Nat.pair c ii)

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

@[simp] theorem eqB_packT (e c ii : ℕ) : eqB (packT e c ii) = e := by
  simp only [eqB, packT, unpair_pair_fst]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

@[simp] theorem consB_packT (e c ii : ℕ) : consB (packT e c ii) = c := by
  simp only [consB, packT, unpair_pair_fst, unpair_pair_snd]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

@[simp] theorem intI_packT (e c ii : ℕ) : intI (packT e c ii) = ii := by
  simp only [intI, packT, unpair_pair_snd]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- **The `D^§` decider step.** `p = pair (pair i j) tbl`. Returns `packT eqBit consBit interIdx`,
case-splitting on `i = 0` / `j = 0` (the `Γ` identity), then on parities (leaf `2a+1` vs node
`2a+2`). Leaf∩leaf delegates to `D`'s deciders; node∩node ANDs/combines the two children read from
the memo table `tbl`. -/
def dsharpStep (p : ℕ) : ℕ :=
  let i := p.unpair.1.unpair.1
  let j := p.unpair.1.unpair.2
  let tbl := p.unpair.2
  let w := p.unpair.1
  let na := i / 2 - 1
  let nb := j / 2 - 1
  let r1 := listGet tbl (w - 1 - Nat.pair na.unpair.1 nb.unpair.1)
  let r2 := listGet tbl (w - 1 - Nat.pair na.unpair.2 nb.unpair.2)
  selectFn (1 - i) (packT (1 - j) 1 j)
    (selectFn (1 - j) (packT (1 - i) 1 i)
      (selectFn (i % 2)
        (selectFn (j % 2)
          (packT (feq (Nat.pair (i / 2) (j / 2))) (fcons (Nat.pair (i / 2) (j / 2)))
            (2 * finter (Nat.pair (i / 2) (j / 2)) + 1))
          (packT 0 0 0))
        (selectFn (j % 2) (packT 0 0 0)
          (packT (eqB r1 * eqB r2) (consB r1 * consB r2)
            (2 * Nat.pair (intI r1) (intI r2) + 2)))))

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharpStep_i0 (j tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair 0 j) tbl) = packT (1 - j) 1 j := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd, Nat.sub_zero, selectFn_one]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharpStep_j0 {i : ℕ} (tbl : ℕ) (hi : i ≠ 0) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair i 0) tbl) = packT (1 - i) 1 i := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - i = 0 by omega, selectFn_zero, Nat.sub_zero, selectFn_one]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharpStep_ll (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 1) (2 * b + 1)) tbl)
      = packT (feq (Nat.pair a b)) (fcons (Nat.pair a b)) (2 * finter (Nat.pair a b) + 1) := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 1) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 1) = 0 by omega, selectFn_zero,
    show (2 * a + 1) % 2 = 1 by omega, selectFn_one,
    show (2 * b + 1) % 2 = 1 by omega, selectFn_one,
    show (2 * a + 1) / 2 = a by omega, show (2 * b + 1) / 2 = b by omega]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharpStep_ln (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 1) (2 * b + 2)) tbl) = packT 0 0 0 := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 1) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 2) = 0 by omega, selectFn_zero,
    show (2 * a + 1) % 2 = 1 by omega, selectFn_one,
    show (2 * b + 2) % 2 = 0 by omega, selectFn_zero]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharpStep_nl (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 2) (2 * b + 1)) tbl) = packT 0 0 0 := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 2) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 1) = 0 by omega, selectFn_zero,
    show (2 * a + 2) % 2 = 0 by omega, selectFn_zero,
    show (2 * b + 1) % 2 = 1 by omega, selectFn_one]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharpStep_nn (a b tbl : ℕ) :
    dsharpStep fcons feq finter (Nat.pair (Nat.pair (2 * a + 2) (2 * b + 2)) tbl)
      = packT
          (eqB (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.1 b.unpair.1))
            * eqB (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.2 b.unpair.2)))
          (consB (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.1 b.unpair.1))
            * consB (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.2 b.unpair.2)))
          (2 * Nat.pair
            (intI (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.1 b.unpair.1)))
            (intI (listGet tbl (Nat.pair (2 * a + 2) (2 * b + 2) - 1 - Nat.pair a.unpair.2 b.unpair.2)))
            + 2) := by
  simp only [dsharpStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 2) = 0 by omega, selectFn_zero,
    show (1 : ℕ) - (2 * b + 2) = 0 by omega, selectFn_zero,
    show (2 * a + 2) % 2 = 0 by omega, selectFn_zero,
    show (2 * b + 2) % 2 = 0 by omega, selectFn_zero,
    show (2 * a + 2) / 2 - 1 = a by omega, show (2 * b + 2) / 2 - 1 = b by omega]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

theorem pair_lt_succ_sq (x y : ℕ) : Nat.pair x y < (max x y + 1) * (max x y + 1) := by
  have hm : ∀ z : ℕ, (z + 1) * (z + 1) = z * z + 2 * z + 1 := fun z => by
    rw [Nat.succ_mul, Nat.mul_succ]; omega
  unfold Nat.pair
  rcases lt_or_ge x y with h | h
  · rw [ite_eq_left h, show max x y = y by omega, hm]; omega
  · rw [ite_eq_right (by omega), show max x y = x by omega, hm]; omega

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

theorem pair_lt_pair_of_lt {x y i j : ℕ} (hx : x < i) (hy : y < j) :
    Nat.pair x y < Nat.pair i j := by
  have h1 : Nat.pair x y < (max x y + 1) * (max x y + 1) := pair_lt_succ_sq x y
  have h2 : max i j * max i j ≤ Nat.pair i j := max_sq_le_pair i j
  have h3 : max x y + 1 ≤ max i j := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; have := le_max_right i j; omega
    · rw [max_eq_left h]; have := le_max_left i j; omega
  have h4 : (max x y + 1) * (max x y + 1) ≤ max i j * max i j := Nat.mul_le_mul h3 h3
  omega

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `listGet` is primitive recursive (on the `Nat.pair` coding of `c, i`). -/
theorem primrec_listGet : Nat.Primrec (fun p => listGet p.unpair.1 p.unpair.2) := by
  have hstp : Nat.Primrec listGetStp := by
    unfold listGetStp
    have hcd : Nat.Primrec (fun t => t.unpair.2.unpair.1.unpair.1) :=
      Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
    have hval : Nat.Primrec (fun t => t.unpair.2.unpair.1.unpair.2) :=
      Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
    have hx : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
    exact (primrec_sub₂ hcd (Nat.Primrec.const 1)).pair
      (primrec_selectFn (primrec_isOne.comp hcd) hx hval)
  have hz : Nat.Primrec (fun p : ℕ => Nat.pair (p.unpair.2 + 1) 0) :=
    (Nat.Primrec.succ.comp Nat.Primrec.right).pair (Nat.Primrec.const 0)
  exact (Nat.Primrec.right.comp
    (primrec_foldCode hstp (Nat.Primrec.const 0) hz Nat.Primrec.left)).of_eq fun p => rfl

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `listGet` as a binary primrec composite. -/
theorem primrec_listGet₂ {c i : ℕ → ℕ} (hc : Nat.Primrec c) (hi : Nat.Primrec i) :
    Nat.Primrec (fun p => listGet (c p) (i p)) :=
  (primrec_listGet.comp (hc.pair hi)).of_eq fun p => by
    simp only [unpair_pair_fst, unpair_pair_snd]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- The decider step is primitive recursive when the `D`-level functions are. -/
theorem primrec_dsharpStep (hfcons : Nat.Primrec fcons) (hfeq : Nat.Primrec feq)
    (hfinter : Nat.Primrec finter) : Nat.Primrec (dsharpStep fcons feq finter) := by
  have hi : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hj : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have htbl : Nat.Primrec (fun p : ℕ => p.unpair.2) := Nat.Primrec.right
  have hw : Nat.Primrec (fun p : ℕ => p.unpair.1) := Nat.Primrec.left
  have hidiv : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1 / 2) := primrec_div2.comp hi
  have hjdiv : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2 / 2) := primrec_div2.comp hj
  have hna : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1 / 2 - 1) :=
    primrec_sub₂ hidiv (Nat.Primrec.const 1)
  have hnb : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2 / 2 - 1) :=
    primrec_sub₂ hjdiv (Nat.Primrec.const 1)
  have hv1 : Nat.Primrec (fun p : ℕ =>
      Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1 (p.unpair.1.unpair.2 / 2 - 1).unpair.1) :=
    (Nat.Primrec.left.comp hna).pair (Nat.Primrec.left.comp hnb)
  have hv2 : Nat.Primrec (fun p : ℕ =>
      Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2 (p.unpair.1.unpair.2 / 2 - 1).unpair.2) :=
    (Nat.Primrec.right.comp hna).pair (Nat.Primrec.right.comp hnb)
  have hr1 : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
        (p.unpair.1.unpair.2 / 2 - 1).unpair.1)) :=
    primrec_listGet₂ htbl (primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1)) hv1)
  have hr2 : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
        (p.unpair.1.unpair.2 / 2 - 1).unpair.2)) :=
    primrec_listGet₂ htbl (primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1)) hv2)
  have hidiv2 : Nat.Primrec (fun p : ℕ => Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)) :=
    hidiv.pair hjdiv
  have hpackT : ∀ {e c ii : ℕ → ℕ}, Nat.Primrec e → Nat.Primrec c → Nat.Primrec ii →
      Nat.Primrec (fun p => packT (e p) (c p) (ii p)) := by
    intro e c ii he hc hii
    exact (he.pair (hc.pair hii)).of_eq fun p => rfl
  have hleaf : Nat.Primrec (fun p : ℕ =>
      packT (feq (Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)))
        (fcons (Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)))
        (2 * finter (Nat.pair (p.unpair.1.unpair.1 / 2) (p.unpair.1.unpair.2 / 2)) + 1)) :=
    hpackT (hfeq.comp hidiv2) (hfcons.comp hidiv2)
      (Nat.Primrec.succ.comp (primrec_mul₂ (Nat.Primrec.const 2) (hfinter.comp hidiv2)))
  have hzero : Nat.Primrec (fun _ : ℕ => packT 0 0 0) := Nat.Primrec.const _
  have heqB1 : Nat.Primrec (fun p => eqB _) := Nat.Primrec.left.comp hr1
  have heqB2 : Nat.Primrec (fun p => eqB _) := Nat.Primrec.left.comp hr2
  have hconsB1 : Nat.Primrec (fun p => consB _) := (Nat.Primrec.left.comp Nat.Primrec.right).comp hr1
  have hconsB2 : Nat.Primrec (fun p => consB _) := (Nat.Primrec.left.comp Nat.Primrec.right).comp hr2
  have hintI1 : Nat.Primrec (fun p => intI _) := (Nat.Primrec.right.comp Nat.Primrec.right).comp hr1
  have hintI2 : Nat.Primrec (fun p => intI _) := (Nat.Primrec.right.comp Nat.Primrec.right).comp hr2
  have hnode : Nat.Primrec (fun p : ℕ =>
      packT (eqB (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                (p.unpair.1.unpair.2 / 2 - 1).unpair.1))
            * eqB (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                (p.unpair.1.unpair.2 / 2 - 1).unpair.2)))
        (consB (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                (p.unpair.1.unpair.2 / 2 - 1).unpair.1))
            * consB (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                (p.unpair.1.unpair.2 / 2 - 1).unpair.2)))
        (2 * Nat.pair (intI (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                (p.unpair.1.unpair.2 / 2 - 1).unpair.1)))
              (intI (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                (p.unpair.1.unpair.2 / 2 - 1).unpair.2))) + 2)) :=
    hpackT (primrec_mul₂ heqB1 heqB2) (primrec_mul₂ hconsB1 hconsB2)
      ((Nat.Primrec.succ.comp Nat.Primrec.succ).comp (primrec_mul₂ (Nat.Primrec.const 2)
        (hintI1.pair hintI2)))
  refine (primrec_selectFn (primrec_sub₂ (Nat.Primrec.const 1) hi)
    (hpackT (primrec_sub₂ (Nat.Primrec.const 1) hj) (Nat.Primrec.const 1) hj)
    (primrec_selectFn (primrec_sub₂ (Nat.Primrec.const 1) hj)
      (hpackT (primrec_sub₂ (Nat.Primrec.const 1) hi) (Nat.Primrec.const 1) hi)
      (primrec_selectFn (primrec_mod2.comp hi)
        (primrec_selectFn (primrec_mod2.comp hj) hleaf hzero)
        (primrec_selectFn (primrec_mod2.comp hj) hzero hnode)))).of_eq fun p => rfl

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The reverse memo table: `rtbl step w` codes `[g(w-1), …, g 0]`. -/
def rtbl (step : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (w + 1) => Nat.pair (step (Nat.pair w (rtbl step w))) (rtbl step w) + 1

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The course-of-values value at `w`: `g w = step (pair w (table of g below w))`. -/
def gOf (step : ℕ → ℕ) (w : ℕ) : ℕ := step (Nat.pair w (rtbl step w))

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The reverse list of memo values `[g(w-1), …, g 0]`. -/
def gList (step : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | (w + 1) => gOf step w :: gList step w

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem gOf_def (step : ℕ → ℕ) (w : ℕ) : gOf step w = step (Nat.pair w (rtbl step w)) := rfl

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem getD_gList (step : ℕ → ℕ) : ∀ (w p : ℕ), p < w →
    (gList step w).getD p 0 = gOf step (w - 1 - p) := by
  intro w
  induction w with
  | zero => intro p hp; omega
  | succ w ih =>
      intro p hp
      cases p with
      | zero =>
          rw [gList, List.getD_cons_zero]
          have : w + 1 - 1 - 0 = w := by omega
          rw [this]
      | succ p =>
          rw [gList, List.getD_cons_succ, ih p (by omega)]
          have : w + 1 - 1 - (p + 1) = w - 1 - p := by omega
          rw [this]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem rtbl_eq_encode (step : ℕ → ℕ) (w : ℕ) : rtbl step w = encodeList (gList step w) := by
  induction w with
  | zero => rfl
  | succ w ih =>
      show Nat.pair (step (Nat.pair w (rtbl step w))) (rtbl step w) + 1
        = encodeList (gList step (w + 1))
      rw [gList, encodeList, gOf, ih]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The course-of-values lookup.** Inside `step` at `w`, position `w-1-v` of the reverse table is
exactly `g v`, for any earlier `v < w`. -/
theorem listGet_rtbl (step : ℕ → ℕ) {v w : ℕ} (hv : v < w) :
    listGet (rtbl step w) (w - 1 - v) = gOf step v := by
  rw [rtbl_eq_encode, listGet_encodeList, getD_gList step w (w - 1 - v) (by omega)]
  congr 1; omega

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem rtbl_eq_rec (step : ℕ → ℕ) (w : ℕ) :
    rtbl step w
      = Nat.rec (motive := fun _ => ℕ) 0
          (fun y IH => Nat.pair (step (Nat.pair y IH)) IH + 1) w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [rtbl, ih]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `rtbl step` is primitive recursive when `step` is (a single `prec` whose step is a cons). -/
theorem primrec_rtbl {step : ℕ → ℕ} (hstep : Nat.Primrec step) : Nat.Primrec (rtbl step) := by
  have hg : Nat.Primrec (fun c => Nat.pair (step c.unpair.2) c.unpair.2.unpair.2 + 1) :=
    Nat.Primrec.succ.comp ((hstep.comp Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.right))
  refine ((Nat.Primrec.prec Nat.Primrec.zero hg).comp
    (Nat.Primrec.zero.pair primrec_id)).of_eq fun w => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rtbl_eq_rec]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `gOf step` is primitive recursive when `step` is. -/
theorem primrec_gOf {step : ℕ → ℕ} (hstep : Nat.Primrec step) : Nat.Primrec (gOf step) :=
  (hstep.comp (primrec_id.pair (primrec_rtbl hstep))).of_eq fun _ => rfl

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

/-- `n.unpair.1 ≤ n` (choice-free); the decreasing measure for `Vsharp`'s left child. -/
theorem unpair_fst_le (n : ℕ) : n.unpair.1 ≤ n := by
  have h := le_pair_left n.unpair.1 n.unpair.2
  rwa [pair_unpair] at h

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

end Proposition77
end
end DomainTheory.NeighbourhoodSystems
end
