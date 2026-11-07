module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.dsharpEffective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.prodEffective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap IndefProduct

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

def proj1Map : ApproximableMap (Dsharp D hD) (Dsharp D hD) where
  rel W Z := MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Qq ⊆ Z)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨MemS.gamma, MemS.gamma, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hd⟩ ⟨-, hZ', hd'⟩
    have hgZ : Z ⊆ Gamma D := memS_subset_gamma hZ
    have hgZ' : Z' ⊆ Gamma D := memS_subset_gamma hZ'
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hQZ⟩
    · rw [Set.inter_eq_right.mpr hgZ']; exact ⟨hW, hZ', hd'⟩
    · rcases hd' with rfl | ⟨Pp', Qq', hWeq', hQZ'⟩
      · rw [Set.inter_eq_left.mpr hgZ]; exact ⟨hW, hZ, Or.inr ⟨Pp, Qq, hWeq, hQZ⟩⟩
      · have hQQ : Qq = Qq' := (embPair_injective (hWeq.symm.trans hWeq')).2
        have hQsub : Qq ⊆ Z ∩ Z' := Set.subset_inter hQZ (by rw [hQQ]; exact hQZ')
        have hMemQ : MemS D Qq := (memS_embPair_inv hD (hWeq ▸ hW)).2
        exact ⟨hW, memS_inter hD hZ hZ' hMemQ hQsub, Or.inr ⟨Pp, Qq, hWeq, hQsub⟩⟩
  mono := by
    rintro W W' Z Z' ⟨hW, hZ, hd⟩ hW'W hZZ' hW'mem hZ'mem
    refine ⟨hW'mem, hZ'mem, ?_⟩
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hQZ⟩
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hZ'mem) hZZ')
    · subst hWeq
      cases hW'mem with
      | gamma =>
        exact absurd (Set.Subset.antisymm (memS_subset_gamma hW) hW'W)
          (embPair_ne_Gamma D hD Pp Qq)
      | @zero X hX =>
        exfalso
        obtain ⟨a, ha⟩ := hD X hX
        rcases hW'W (show (([], a) : List Bool × α) ∈ embZero X from ⟨rfl, ha⟩) with
          ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'
      | @pair Pp' Qq' hP' hQ' =>
        obtain ⟨-, hQ'Q⟩ := embPair_subset.mp hW'W
        exact Or.inr ⟨Pp', Qq', rfl, fun z hz => hZZ' (hQZ (hQ'Q hz))⟩

@[simp] theorem proj1Map_rel {W Z : Set (List Bool × α)} :
    (proj1Map hD).rel W Z ↔
      MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Qq ⊆ Z) := Iff.rfl

def pairSharpMap : ApproximableMap (prod (Dsharp D hD) (Dsharp D hD)) (Dsharp D hD) where
  rel V W := (prod (Dsharp D hD) (Dsharp D hD)).mem V ∧ MemS D W ∧
    ∃ A B, MemS D A ∧ MemS D B ∧ V = prodNbhd A B ∧ embPair A B ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod (Dsharp D hD) (Dsharp D hD)).master_mem, MemS.gamma,
    ⟨Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl, embPair_subset_Gamma subset_rfl subset_rfl⟩⟩
  inter_right := by
    rintro V W W' ⟨hV, hW, A, B, hA, hB, rfl, hsub⟩ ⟨-, hW', A', B', hA', hB', heq, hsub'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd.injective heq
    exact ⟨hV, memS_inter hD hW hW' (MemS.pair hA hB) (Set.subset_inter hsub hsub'),
      A, B, hA, hB, rfl, Set.subset_inter hsub hsub'⟩
  mono := by
    rintro V V' W W' ⟨hV, hW, A, B, hA, hB, rfl, hsub⟩ hV'V hWW' hV'mem hW'mem
    obtain ⟨A', B', hA', hB', rfl⟩ := hV'mem
    obtain ⟨hA'A, hB'B⟩ := prodNbhd.subset_iff.mp hV'V
    exact ⟨prod_mem_prodNbhd hA' hB', hW'mem, A', B', hA', hB', rfl,
      (embPair_subset.mpr ⟨hA'A, hB'B⟩).trans (hsub.trans hWW')⟩

@[simp] theorem pairSharpMap_rel {V : Set ((List Bool × α) ⊕ (List Bool × α))}
    {W : Set (List Bool × α)} :
    (pairSharpMap hD).rel V W ↔
      (prod (Dsharp D hD) (Dsharp D hD)).mem V ∧ MemS D W ∧
        ∃ A B, MemS D A ∧ MemS D B ∧ V = prodNbhd A B ∧ embPair A B ⊆ W := Iff.rfl

theorem pairSharpMap_toElementMap (x y : (Dsharp D hD).Element) :
    (pairSharpMap hD).toElementMap (DomainTheory.NeighbourhoodSystems.pair x y) = pairSharp D hD x y := by
  apply Element.ext
  intro W
  simp only [ApproximableMap.mem_toElementMap, pairSharpMap_rel, mem_pair]
  constructor
  · rintro ⟨V, ⟨A0, B0, hxA0, hyB0, rfl⟩, -, hW, A, B, -, -, heq, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd.injective heq
    exact (pairSharp D hD x y).up_mem (Or.inr ⟨A0, B0, hxA0, hyB0, rfl⟩) hW hsub
  · intro hW
    rcases hW with rfl | ⟨P, Q, hxP, hyQ, rfl⟩
    · exact ⟨prodNbhd (Gamma D) (Gamma D), ⟨Gamma D, Gamma D, x.master_mem, y.master_mem, rfl⟩,
        ⟨Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl⟩, MemS.gamma,
        Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl,
        embPair_subset_Gamma subset_rfl subset_rfl⟩
    · exact ⟨prodNbhd P Q, ⟨P, Q, hxP, hyQ, rfl⟩, prod_mem_prodNbhd (x.sub hxP) (y.sub hyQ),
        MemS.pair (x.sub hxP) (y.sub hyQ), P, Q, x.sub hxP, y.sub hyQ, rfl, subset_rfl⟩

theorem pairSharp_rel_Vsharp_iff (P : ComputablePresentation D) (t k : ℕ) :
    (pairSharpMap hD).rel
        ((prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD)).X t)
        ((dsharpPresentation P hD).X k) ↔
      Vsharp D P (2 * t + 2) ⊆ Vsharp D P k := by
  rw [pairSharpMap_rel, prodPresentation_X, Vsharp_even]
  constructor
  · rintro ⟨-, -, A, B, -, -, heq, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd.injective heq
    exact hsub
  · intro hsub
    exact ⟨prod_mem_prodNbhd (Vsharp_mem P _) (Vsharp_mem P _), Vsharp_mem P k,
      _, _, Vsharp_mem P _, Vsharp_mem P _, rfl, hsub⟩

end Proposition77
end
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive IndefProduct ApproximableMap
section
variable {α : Type*}
namespace Proposition77
variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

theorem pairSharp_isComputable (P : ComputablePresentation D) :
    ComputableMap (prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD))
      (dsharpPresentation P hD) (pairSharpMap hD) := by
  constructor
  show REPred (fun s => (pairSharpMap hD).rel
    ((prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD)).X s.unpair.1)
    ((dsharpPresentation P hD).X s.unpair.2))
  have hincl : RecDecidable (fun s => Vsharp D P s.unpair.1 ⊆ Vsharp D P s.unpair.2) :=
    (dsharpPresentation P hD).incl_computable
  have hr : Nat.Primrec (fun s => Nat.pair (2 * s.unpair.1 + 2) s.unpair.2) :=
    (primrec_add₂ (primrec_mul₂ (Nat.Primrec.const 2) Nat.Primrec.left)
      (Nat.Primrec.const 2)).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun s => ?_) (hincl.comp hr)).re
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [pairSharp_rel_Vsharp_iff hD P s.unpair.1 s.unpair.2]

theorem proj1_rel_Vsharp_iff (P : ComputablePresentation D) (m k : ℕ) :
    (proj1Map hD).rel (Vsharp D P m) (Vsharp D P k) ↔
      k = 0 ∨ (m % 2 = 0 ∧ m ≠ 0 ∧ Vsharp D P (m / 2 - 1).unpair.2 ⊆ Vsharp D P k) := by
  rw [proj1Map_rel, and_iff_right (Vsharp_mem P m), and_iff_right (Vsharp_mem P k)]
  refine or_congr (Vsharp_eq_Gamma_iff P hD k) ?_
  rcases nat_shape m with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [Vsharp_zero]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq.symm (embPair_ne_Gamma D hD Pp Qq)
    · rintro ⟨-, hne, -⟩; exact absurd rfl hne
  · rw [Vsharp_odd]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq (embZero_ne_embPair D hD (P.mem_X a) Pp Qq)
    · rintro ⟨hmod, -, -⟩; exact absurd hmod (by omega)
  · rw [Vsharp_even, show (2 * a + 2) / 2 - 1 = a from by omega]
    constructor
    · rintro ⟨Pp, Qq, heq, hQk⟩
      obtain ⟨-, hQ⟩ := embPair_injective heq
      exact ⟨by omega, by omega, by rw [hQ]; exact hQk⟩
    · rintro ⟨-, -, hsub⟩
      exact ⟨Vsharp D P a.unpair.1, Vsharp D P a.unpair.2, rfl, hsub⟩

theorem proj1_isComputable (P : ComputablePresentation D) :
    ComputableMap (dsharpPresentation P hD) (dsharpPresentation P hD) (proj1Map hD) := by
  constructor
  show REPred (fun s => (proj1Map hD).rel (Vsharp D P s.unpair.1) (Vsharp D P s.unpair.2))
  have hk0 : RecDecidable (fun s => s.unpair.2 = 0) :=
    RecDecidable.natEq Nat.Primrec.right (Nat.Primrec.const 0)
  have hmod : RecDecidable (fun s => s.unpair.1 % 2 = 0) :=
    RecDecidable.natEq (primrec_mod2.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hne : RecDecidable (fun s => s.unpair.1 ≠ 0) :=
    (RecDecidable.natEq Nat.Primrec.left (Nat.Primrec.const 0)).not
  have hg : Nat.Primrec (fun s => Nat.pair (s.unpair.1 / 2 - 1).unpair.2 s.unpair.2) :=
    (Nat.Primrec.right.comp (primrec_sub₂ (primrec_div2.comp Nat.Primrec.left)
      (Nat.Primrec.const 1))).pair Nat.Primrec.right
  have hincl : RecDecidable (fun s => Vsharp D P (s.unpair.1 / 2 - 1).unpair.2 ⊆
      Vsharp D P s.unpair.2) := by
    refine RecDecidable.of_iff (fun s => ?_) ((dsharpPresentation P hD).incl_computable.comp hg)
    simp only [dsharpPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact (RecDecidable.of_iff (fun s => proj1_rel_Vsharp_iff hD P s.unpair.1 s.unpair.2)
    (hk0.or (hmod.and (hne.and hincl)))).re

end Proposition77
end
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap IndefProduct
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

theorem proj1_toElementMap_pairSharp (x y : (Dsharp D hD).Element) :
    (proj1Map hD).toElementMap (pairSharp D hD x y) = y := by
  apply Element.ext
  intro Z
  simp only [ApproximableMap.mem_toElementMap, proj1Map_rel]
  constructor
  · rintro ⟨W, hWmem, hMW, hMZ, hdisj⟩
    rcases hWmem with rfl | ⟨Pp, Qq, hxP, hyQ, rfl⟩
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, -⟩
      · exact y.master_mem
      · exact absurd hPe.symm (embPair_ne_Gamma D hD Pp' Qq')
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, hQ'Z⟩
      · exact y.master_mem
      · obtain ⟨-, hQQ⟩ := embPair_injective hPe
        exact y.up_mem hyQ hMZ (by rw [hQQ]; exact hQ'Z)
  · intro hyZ
    exact ⟨embPair (Gamma D) Z, Or.inr ⟨Gamma D, Z, x.master_mem, hyZ, rfl⟩,
      MemS.pair MemS.gamma (y.sub hyZ), y.sub hyZ, Or.inr ⟨Gamma D, Z, rfl, subset_rfl⟩⟩

end Proposition77
end
end DomainTheory.NeighbourhoodSystems
