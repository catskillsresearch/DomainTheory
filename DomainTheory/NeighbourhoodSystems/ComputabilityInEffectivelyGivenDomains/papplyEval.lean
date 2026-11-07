module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_19
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_11
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_10
public import DomainTheory.NeighbourhoodSystems.DomainEquations.indefProduct
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem_6_9

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β : Type*}

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

@[simp] theorem papplyEval_rel {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {Φ : Set (Set (ApproximableMap V W))} {A : Set (Set α)} {B : Set (Set β)} :
    (papplyEval V W).rel Φ A B ↔ (funSpace V W).PDmem Φ ∧ V.PDmem A ∧ W.PDmem B ∧
      ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, (eval V W).rel G X Y := Iff.rfl

def papplyB (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V W).PowerDomain V.PowerDomain) W.PowerDomain :=
  ofMap₂ (papplyEval V W)

def papply (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (funSpace V W).PowerDomain (funSpace V.PowerDomain W.PowerDomain) :=
  curry (papplyB V W)

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

theorem re_forallG_forallX_existsY {R : ℕ → ℕ → ℕ → Prop}
    (hR : REPred (fun s => R s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2)) :
    REPred (fun w => ∀ g ∈ decodeList w.unpair.1, ∀ x ∈ decodeList w.unpair.2.unpair.1,
      ∃ y ∈ decodeList w.unpair.2.unpair.2, R g x y) := by

  have hm1 : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.1.unpair.1
      (Nat.pair s.unpair.1.unpair.2 s.unpair.2)) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair
      ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
  have hR2 : REPred₂ (fun gx y => R gx.unpair.1 gx.unpair.2 y) := by
    show REPred (fun t => R t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2)
    refine REPred.of_iff (fun s => ?_) (hR.comp hm1)
    simp only [unpair_pair_fst, unpair_pair_snd]

  have hE : REPred (fun u => ∃ b ∈ decodeList u.unpair.1,
      R u.unpair.2.unpair.1 u.unpair.2.unpair.2 b) := bExists_decodeList_re hR2

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

  have hm4 : Nat.Primrec (fun w : ℕ => Nat.pair
      (Nat.pair w.unpair.2.unpair.2 w.unpair.2.unpair.1) w.unpair.1) :=
    ((Nat.Primrec.right.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.comp Nat.Primrec.right)).pair Nat.Primrec.left
  refine REPred.of_iff (fun w => ?_) (hGfull.comp hm4)
  simp only [unpair_pair_fst, unpair_pair_snd]

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

end DomainTheory.NeighbourhoodSystems
