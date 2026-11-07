module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.ProjectionMappings
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.inducedMaps
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive IndefProduct ApproximableMap

section
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


def prodEnum (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) (t : ℕ) :
    Set (α ⊕ β) :=
  prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2)

@[simp] theorem prodEnum_apply (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (t : ℕ) : prodEnum P₀ P₁ t = prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2) := rfl


theorem prodNbhd_eq_iff {X X' : Set α} {Y Y' : Set β} :
    prodNbhd X Y = prodNbhd X' Y' ↔ X = X' ∧ Y = Y' :=
  ⟨prodNbhd.injective, by rintro ⟨rfl, rfl⟩; rfl⟩

def prodPresentation (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputablePresentation (prod V₀ V₁) where
  X := prodEnum P₀ P₁
  mem_X t := prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _)
  surj := by
    rintro Z ⟨X, Y, hX, hY, rfl⟩
    obtain ⟨n, rfl⟩ := P₀.surj hX
    obtain ⟨m, rfl⟩ := P₁.surj hY
    exact ⟨Nat.pair n m, by simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd]⟩
  interEq_computable := by
    have hIE0 : RecDecidable (fun s => P₀.X s.unpair.1 ∩ P₀.X s.unpair.2.unpair.1
        = P₀.X s.unpair.2.unpair.2) := P₀.interEq_computable
    have hIE1 : RecDecidable (fun s => P₁.X s.unpair.1 ∩ P₁.X s.unpair.2.unpair.1
        = P₁.X s.unpair.2.unpair.2) := P₁.interEq_computable
    have hg0 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1
        (Nat.pair t.unpair.2.unpair.1.unpair.1 t.unpair.2.unpair.2.unpair.1)) :=
      (Nat.Primrec.left.comp Nat.Primrec.left).pair
        ((Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    have hg1 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2
        (Nat.pair t.unpair.2.unpair.1.unpair.2 t.unpair.2.unpair.2.unpair.2)) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair
        ((Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_) ((hIE0.comp hg0).and (hIE1.comp hg1))
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd, prodNbhd.inter, prodNbhd_eq_iff]
  cons_computable := by
    have hC0 : RecDecidable (fun s => ∃ k, P₀.X k ⊆ P₀.X s.unpair.1 ∩ P₀.X s.unpair.2) :=
      P₀.cons_computable
    have hC1 : RecDecidable (fun s => ∃ k, P₁.X k ⊆ P₁.X s.unpair.1 ∩ P₁.X s.unpair.2) :=
      P₁.cons_computable
    have hh0 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1) :=
      (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.left.comp Nat.Primrec.right)
    have hh1 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2.unpair.2) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)
    refine RecDecidable.of_iff (fun t => ?_) ((hC0.comp hh0).and (hC1.comp hh1))
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd, prodNbhd.inter,
      prodNbhd.subset_iff]
    constructor
    · rintro ⟨k, hk0, hk1⟩
      exact ⟨⟨k.unpair.1, hk0⟩, ⟨k.unpair.2, hk1⟩⟩
    · rintro ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩⟩
      exact ⟨Nat.pair k0 k1, by simpa only [unpair_pair_fst] using hk0,
        by simpa only [unpair_pair_snd] using hk1⟩
  inter n m := Nat.pair (P₀.inter n.unpair.1 m.unpair.1) (P₁.inter n.unpair.2 m.unpair.2)
  inter_primrec := by
    have h0 : Nat.Primrec (fun t => P₀.inter t.unpair.1.unpair.1 t.unpair.2.unpair.1) :=
      (P₀.inter_primrec.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair
        (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq fun t => by
          simp only [unpair_pair_fst, unpair_pair_snd]
    have h1 : Nat.Primrec (fun t => P₁.inter t.unpair.1.unpair.2 t.unpair.2.unpair.2) :=
      (P₁.inter_primrec.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right))).of_eq fun t => by
          simp only [unpair_pair_fst, unpair_pair_snd]
    exact h0.pair h1
  inter_spec := by
    rintro n m ⟨k, hk⟩
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd] at hk ⊢
    rw [prodNbhd.inter] at hk ⊢
    obtain ⟨h0, h1⟩ := prodNbhd.subset_iff.mp hk
    rw [P₀.inter_spec ⟨_, h0⟩, P₁.inter_spec ⟨_, h1⟩]
  masterIdx := Nat.pair P₀.masterIdx P₁.masterIdx
  masterIdx_spec := by
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd, P₀.masterIdx_spec,
      P₁.masterIdx_spec, prod_master]

@[simp] theorem prodPresentation_X (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (t : ℕ) :
    (prodPresentation P₀ P₁).X t = prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2) := rfl

theorem paired_isComputable {V₂ : NeighborhoodSystem γ}
    {P₂ : ComputablePresentation V₂} {P₀ : ComputablePresentation V₀}
    {P₁ : ComputablePresentation V₁} {a : ApproximableMap V₂ V₀} {b : ApproximableMap V₂ V₁}
    (ha : ComputableMap P₂ P₀ a) (hb : ComputableMap P₂ P₁ b) :
    ComputableMap P₂ (prodPresentation P₀ P₁) (paired a b) := by
  constructor
  have ha' : REPred (fun s => a.rel (P₂.X s.unpair.1) (P₀.X s.unpair.2)) := ha.out
  have hb' : REPred (fun s => b.rel (P₂.X s.unpair.1) (P₁.X s.unpair.2)) := hb.out
  have hra : Nat.Primrec (fun t => Nat.pair t.unpair.1 t.unpair.2.unpair.1) :=
    Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right)
  have hrb : Nat.Primrec (fun t => Nat.pair t.unpair.1 t.unpair.2.unpair.2) :=
    Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  refine REPred.of_iff (fun t => ?_) ((ha'.comp hra).and (hb'.comp hrb))
  simp only [prodPresentation_X, paired_rel, prodNbhd.inl_preimage, prodNbhd.inr_preimage,
    unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), h.1, h.2⟩⟩

theorem prod_isEffectivelyGiven (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (prod V₀ V₁).IsEffectivelyGiven := by
  obtain ⟨P₀⟩ := h₀; obtain ⟨P₁⟩ := h₁
  exact ⟨prodPresentation P₀ P₁⟩

theorem proj₀_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputableMap (prodPresentation P₀ P₁) P₀ (proj₀ V₀ V₁) := by
  constructor
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, proj₀_rel, prodNbhd.inl_preimage, unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => h.2.2,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), P₀.mem_X _, h⟩⟩

theorem proj₁_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputableMap (prodPresentation P₀ P₁) P₁ (proj₁ V₀ V₁) := by
  constructor
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, proj₁_rel, prodNbhd.inr_preimage, unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => h.2.2,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), P₁.mem_X _, h⟩⟩

theorem prodMap_isComputable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}
    {P₀' : ComputablePresentation V₀'} {P₁' : ComputablePresentation V₁'}
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : ComputableMap P₀ P₀' f) (hg : ComputableMap P₁ P₁' g) :
    ComputableMap (prodPresentation P₀ P₁) (prodPresentation P₀' P₁') (prodMap f g) := by
  rw [prodMap]
  exact paired_isComputable (comp_isComputable (proj₀_isComputable P₀ P₁) hf)
    (comp_isComputable (proj₁_isComputable P₀ P₁) hg)

end

end DomainTheory.NeighbourhoodSystems
