module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_4

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive Example61
open NeighborhoodSystem Domain.Recursive ApproximableMap
namespace Exercise718
open NeighborhoodSystem Domain.Recursive ApproximableMap
section
variable {α β : Type*}
/- concordance: source L4655 EXERCISE 7.18 effective isomorphism -/
/-- **Exercise 7.18 (Scott 1981, PRG-19) — effective isomorphism (completing the sentence).** Two
effectively given systems `D` (presentation `P`) and `E` (presentation `Q`) are *effectively
isomorphic* iff there is a pair of mutually inverse approximable maps `toMap : D → E`,
`invMap : E → D`, **both computable** (Definition 7.2). -/
structure EffectiveIso {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) where
  /-- The forward map `D → E`. -/
  toMap : ApproximableMap V W
  /-- The inverse map `E → D`. -/
  invMap : ApproximableMap W V
  /-- The forward map is computable. -/
  toMap_computable : ComputableMap P Q toMap
  /-- The inverse map is computable. -/
  invMap_computable : ComputableMap Q P invMap
  /-- `invMap ∘ toMap = I_D`. -/
  left_inv : invMap.comp toMap = idMap V
  /-- `toMap ∘ invMap = I_E`. -/
  right_inv : toMap.comp invMap = idMap W
end

section
variable {α β : Type*}

/-- **Exercise 7.18 — effectively isomorphic.** `D` and `E` are effectively isomorphic when an
`EffectiveIso` exists. -/
def EffectivelyIsomorphic {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) : Prop :=
  Nonempty (EffectiveIso P Q)
end

end Exercise718
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-- **The second projection of the pair part of `D^§`, as an approximable map.** On the pair summand
`1·P ∪ 2·Q` it returns `Q`; everywhere else it returns `⊥ = {Γ}`. The exact mirror of `proj0Map`
with the *second* component: `W proj₁ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧ Q ⊆ Z`. -/
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

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

@[simp] theorem proj1Map_rel {W Z : Set (List Bool × α)} :
    (proj1Map hD).rel W Z ↔
      MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Qq ⊆ Z) := Iff.rfl

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-- **Example 6.1's pairing constructor `pair : D^§ × D^§ → D^§`, as a joint approximable map.**
`(A ∪ B) pair W ↔ A, B ∈ 𝒟^§ ∧ W ∈ 𝒟^§ ∧ 1·A ∪ 2·B ⊆ W` (with `A ∪ B = prodNbhd A B`). -/
def pairSharpMap : ApproximableMap (prod (Dsharp D hD) (Dsharp D hD)) (Dsharp D hD) where
  rel V W := (prod (Dsharp D hD) (Dsharp D hD)).mem V ∧ MemS D W ∧
    ∃ A B, MemS D A ∧ MemS D B ∧ V = prodNbhd A B ∧ embPair A B ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod (Dsharp D hD) (Dsharp D hD)).master_mem, MemS.gamma,
    ⟨Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl, embPair_subset_Gamma subset_rfl subset_rfl⟩⟩
  inter_right := by
    rintro V W W' ⟨hV, hW, A, B, hA, hB, rfl, hsub⟩ ⟨-, hW', A', B', hA', hB', heq, hsub'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hV, memS_inter hD hW hW' (MemS.pair hA hB) (Set.subset_inter hsub hsub'),
      A, B, hA, hB, rfl, Set.subset_inter hsub hsub'⟩
  mono := by
    rintro V V' W W' ⟨hV, hW, A, B, hA, hB, rfl, hsub⟩ hV'V hWW' hV'mem hW'mem
    obtain ⟨A', B', hA', hB', rfl⟩ := hV'mem
    obtain ⟨hA'A, hB'B⟩ := prodNbhd_subset_iff.mp hV'V
    exact ⟨prod_mem_prodNbhd hA' hB', hW'mem, A', B', hA', hB', rfl,
      (embPair_subset.mpr ⟨hA'A, hB'B⟩).trans (hsub.trans hWW')⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


@[simp] theorem pairSharpMap_rel {V : Set ((List Bool × α) ⊕ (List Bool × α))}
    {W : Set (List Bool × α)} :
    (pairSharpMap hD).rel V W ↔
      (prod (Dsharp D hD) (Dsharp D hD)).mem V ∧ MemS D W ∧
        ∃ A B, MemS D A ∧ MemS D B ∧ V = prodNbhd A B ∧ embPair A B ⊆ W := Iff.rfl
end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **`pairSharpMap` really is Example 6.1's pairing:** `pair(x, y) ↦ ⟨x, y⟩^§` (`pairSharp`). -/
theorem pairSharpMap_toElementMap (x y : (Dsharp D hD).Element) :
    (pairSharpMap hD).toElementMap (DomainTheory.NeighbourhoodSystems.pair x y) = pairSharp D hD x y := by
  apply Element.ext
  intro W
  simp only [ApproximableMap.mem_toElementMap, pairSharpMap_rel, mem_pair]
  constructor
  · rintro ⟨V, ⟨A0, B0, hxA0, hyB0, rfl⟩, -, hW, A, B, -, -, heq, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact (pairSharp D hD x y).up_mem (Or.inr ⟨A0, B0, hxA0, hyB0, rfl⟩) hW hsub
  · intro hW
    rcases hW with rfl | ⟨P, Q, hxP, hyQ, rfl⟩
    · exact ⟨prodNbhd (Gamma D) (Gamma D), ⟨Gamma D, Gamma D, x.master_mem, y.master_mem, rfl⟩,
        ⟨Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl⟩, MemS.gamma,
        Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl,
        embPair_subset_Gamma subset_rfl subset_rfl⟩
    · exact ⟨prodNbhd P Q, ⟨P, Q, hxP, hyQ, rfl⟩, prod_mem_prodNbhd (x.sub hxP) (y.sub hyQ),
        MemS.pair (x.sub hxP) (y.sub hyQ), P, Q, x.sub hxP, y.sub hyQ, rfl, subset_rfl⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- The index characterization of `pairSharpMap` against the product/`Vsharp` enumerations:
`(V⁰_{p t} ∪ V¹_{q t}) pair V_k ↔ V_{2·t+2} ⊆ V_k` (since `V_{2t+2} = 1·V_{p t} ∪ 2·V_{q t}`). -/
theorem pairSharp_rel_Vsharp_iff (P : ComputablePresentation D) (t k : ℕ) :
    (pairSharpMap hD).rel
        ((prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD)).X t)
        ((dsharpPresentation P hD).X k) ↔
      Vsharp D P (2 * t + 2) ⊆ Vsharp D P k := by
  rw [pairSharpMap_rel, prodPresentation_X, Vsharp_even]
  constructor
  · rintro ⟨-, -, A, B, -, -, heq, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hsub
  · intro hsub
    exact ⟨prod_mem_prodNbhd (Vsharp_mem P _) (Vsharp_mem P _), Vsharp_mem P k,
      _, _, Vsharp_mem P _, Vsharp_mem P _, rfl, hsub⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


end Proposition77
end
end DomainTheory.NeighbourhoodSystems
end
