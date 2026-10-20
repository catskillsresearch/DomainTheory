/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr

@[expose] public section

/-!
# Exercise 6.21 (Scott 1981, PRG-19, §6) — the *separated* sum `⊕` and product `⊗`

> **EXERCISE 6.21.** Do the same as 6.19 and 6.20 when the functors are also allowed to be generated
> by the operations
> `D₀ ⊕ D₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {0X ∣ X ∈ D₀ ∖ {Δ₀}} ∪ {1Y ∣ Y ∈ D₁ ∖ {Δ₁}}`,
> `D₀ ⊗ D₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {{Λ} ∪ 0X ∪ 1Y ∣ X ∈ D₀ ∖ {Δ₀} and Y ∈ D₁ ∖ {Δ₁}}`.
> Generalize all of `+`, `×`, `⊕`, `⊗` to combinations of several terms, not just the binary sums and
> products.

This module extends Exercise 6.19 Part B (`Exercise619PartB.lean`) with the two *coalesced*
operations. The difference from the *separated* sum `+`/product `×` of 6.19 is that `⊕`/`⊗` **delete
the improper tagged copies** `0Δ₀` and `1Δ₁`: in domain terms this **identifies the two bottoms**
(`⊕` is the coalesced sum, `⊗` the smash product), whereas `+`/`×` keep them apart. Both share the
*same master* `{Λ} ∪ 0Δ₀ ∪ 1Δ₁` as `+`/`×`.

## Contents (this stage: objects)

* `oplusTok`/`otimesTok` — the two token-level systems over `Str = {0,1}*`, each `∅`-free.
* `ScottSys.oplus`/`ScottSys.otimes` — the same, repackaged as objects of Scott's category.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/-! ## The coalesced sum `D₀ ⊕ D₁` over `{0,1}*`

`D₀ ⊕ D₁ = {M} ∪ {0X ∣ X ∈ 𝒟₀, X ≠ Δ₀} ∪ {1Y ∣ Y ∈ 𝒟₁, Y ≠ Δ₁}`, where `M = {Λ} ∪ 0Δ₀ ∪ 1Δ₁` is
the shared `sumTokMaster`. -/

/-- If `X ⊆ Δ` and `X ≠ Δ`, then any intersection `X ∩ X'` is still `≠ Δ` (it is `⊆ X ⊊ Δ`). -/
theorem inter_ne_of_ne_left {X X' Δ : Set Str} (hX : X ⊆ Δ) (hne : X ≠ Δ) : X ∩ X' ≠ Δ := by
  intro h
  exact hne (Set.Subset.antisymm hX (by rw [← h]; exact Set.inter_subset_left))

/-- **Exercise 6.21 — the coalesced sum system `𝒟₀ ⊕ 𝒟₁` over `{0,1}*`.** As `sumTok`, but the
improper copies `0Δ₀`, `1Δ₁` are removed (`X ≠ Δ₀`, `Y ≠ Δ₁`), so the two bottoms are identified. -/
def oplusTok (D₀ D₁ : NeighborhoodSystem Str)
    (h₀ : ∀ X, D₀.mem X → X.Nonempty) (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ X ≠ D₀.master ∧ W = embBit false X) ∨
    (∃ Y, D₁.mem Y ∧ Y ≠ D₁.master ∧ W = embBit true Y)
  master := sumTokMaster D₀ D₁
  master_nonempty := ⟨[], nil_mem_sumTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_sumTokMaster hX
    · exact embT_subset_sumTokMaster hY
  inter_mem := by
    have hne : ∀ W, (W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ X ≠ D₀.master ∧ W = embBit false X) ∨
        (∃ Y, D₁.mem Y ∧ Y ≠ D₁.master ∧ W = embBit true Y)) → (W : Set Str).Nonempty := by
      rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · exact ⟨[], nil_mem_sumTokMaster⟩
      · exact embBit_nonempty (h₀ X hX)
      · exact embBit_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩)
      · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embF hX]
        exact Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X ∩ X', D₀.inter_mem hX hX' hZ₀ (embBit_subset.mp hZsub),
            inter_ne_of_ne_left (D₀.sub_master hX) hXne, rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          obtain ⟨w', he, -⟩ := hZsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Z₁)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embT hY]
        exact Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)
      · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          obtain ⟨w', he, -⟩ := hZsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false Z₀)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
        · exact Or.inr (Or.inr ⟨Y ∩ Y', D₁.inter_mem hY hY' hZ₁ (embBit_subset.mp hZsub),
            inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩)

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_nonempty : ∀ W, (oplusTok D₀ D₁ h₀ h₁).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
  · exact ⟨[], nil_mem_sumTokMaster⟩
  · exact embBit_nonempty (h₀ X hX)
  · exact embBit_nonempty (h₁ Y hY)

/-! ## The smash product `D₀ ⊗ D₁` over `{0,1}*`

`D₀ ⊗ D₁ = {M} ∪ {{Λ} ∪ 0X ∪ 1Y ∣ X ∈ 𝒟₀, X ≠ Δ₀, Y ∈ 𝒟₁, Y ≠ Δ₁}`, where again
`M = {Λ} ∪ 0Δ₀ ∪ 1Δ₁ = prodTokNbhd Δ₀ Δ₁`. The improper rectangles touching a top coordinate (other
than the full top `M`) are removed. -/

/-- **Exercise 6.21 — the smash product system `𝒟₀ ⊗ 𝒟₁` over `{0,1}*`.** As `prodTok`, but proper
rectangles must avoid both top coordinates (`X ≠ Δ₀`, `Y ≠ Δ₁`); the full top `M = prodTokNbhd Δ₀ Δ₁`
is kept as the master. -/
def otimesTok (D₀ D₁ : NeighborhoodSystem Str) : NeighborhoodSystem Str where
  mem W := W = prodTokNbhd D₀.master D₁.master ∨
    (∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ X ≠ D₀.master ∧ Y ≠ D₁.master ∧ W = prodTokNbhd X Y)
  master := prodTokNbhd D₀.master D₁.master
  master_nonempty := ⟨[], mem_prodTokNbhd_nil⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, Y, hX, hY, -, -, rfl⟩)
    · exact subset_rfl
    · exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, D₁.sub_master hY⟩
  inter_mem := by
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX'),
          Set.inter_eq_right.mpr (D₁.sub_master hY')]
        exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
      · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX),
          Set.inter_eq_right.mpr (D₁.sub_master hY)]
        exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · rw [prodTokNbhd_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, Z₁, hZ₀, hZ₁, -, -, rfl⟩
        · obtain ⟨hsub₀, -⟩ := prodTokNbhd_subset_iff.mp hZsub
          exact absurd (Set.Subset.antisymm (D₀.sub_master hX)
            (hsub₀.trans Set.inter_subset_left)) hXne
        · obtain ⟨hsub₀, hsub₁⟩ := prodTokNbhd_subset_iff.mp hZsub
          exact Or.inr ⟨X ∩ X', Y ∩ Y', D₀.inter_mem hX hX' hZ₀ hsub₀,
            D₁.inter_mem hY hY' hZ₁ hsub₁, inter_ne_of_ne_left (D₀.sub_master hX) hXne,
            inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩

theorem otimesTok_nonempty : ∀ W, (otimesTok D₀ D₁).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, Y, -, -, -, -, rfl⟩) <;> exact ⟨[], mem_prodTokNbhd_nil⟩

/-! ## Repackaged as objects of Scott's category -/

/-- The **coalesced sum object** `𝒟₀ ⊕ 𝒟₁`. -/
def ScottSys.oplus (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨oplusTok A₀.sys A₁.sys A₀.ne A₁.ne, oplusTok_nonempty⟩

/-- The **smash product object** `𝒟₀ ⊗ 𝒟₁`. -/
def ScottSys.otimes (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨otimesTok A₀.sys A₁.sys, otimesTok_nonempty⟩

/-! ## Membership inversions -/

theorem oplusTok_mem_embF {X : Set Str} (hX : D₀.mem X) (hXne : X ≠ D₀.master) :
    (oplusTok D₀ D₁ h₀ h₁).mem (embBit false X) := Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)

theorem oplusTok_mem_embT {Y : Set Str} (hY : D₁.mem Y) (hYne : Y ≠ D₁.master) :
    (oplusTok D₀ D₁ h₀ h₁).mem (embBit true Y) := Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)

theorem otimesTok_mem_master : (otimesTok D₀ D₁).mem (prodTokNbhd D₀.master D₁.master) := Or.inl rfl

theorem otimesTok_mem_prod {X Y : Set Str} (hX : D₀.mem X) (hY : D₁.mem Y)
    (hXne : X ≠ D₀.master) (hYne : Y ≠ D₁.master) :
    (otimesTok D₀ D₁).mem (prodTokNbhd X Y) := Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩

/-! ## Monotone on domains: `◁` is carried componentwise -/

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-! ## The functorial action of the coalesced sum on (strict) maps

The relation has the same shape as `sumMapTok` but with two changes forced by *coalescence*: proper
tagged copies require the components to be proper (`X ≠ Δ₀`, `X' ≠ Δ₀'`), and the **master/collapse
row** `(W ∈ 𝒟₀⊕𝒟₁ ∧ W' = M)` sends *every* neighbourhood to the top `M` (which is always valid, the
top being the least informative output, and is exactly what handles `f₀(X) = Δ₀'` collapsing back to
the shared bottom). -/

variable {C₀ C₁ : ScottSys}

/-- **`f₀ ⊕ f₁`, the action of the coalesced sum on maps.** -/
def oplusMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.oplus A₁).sys (B₀.oplus B₁).sys where
  rel W W' :=
    ((A₀.oplus A₁).sys.mem W ∧ W' = sumTokMaster B₀.sys B₁.sys) ∨
    (∃ X X', f₀.rel X X' ∧ X ≠ A₀.sys.master ∧ X' ≠ B₀.sys.master ∧
      W = embBit false X ∧ W' = embBit false X') ∨
    (∃ Y Y', f₁.rel Y Y' ∧ Y ≠ A₁.sys.master ∧ Y' ≠ B₁.sys.master ∧
      W = embBit true Y ∧ W' = embBit true Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, hXne, -, rfl, -⟩ | ⟨Y, Y', hrel, hYne, -, rfl, -⟩)
    · exact hW
    · exact oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) (f₀.rel_dom hrel) hXne
    · exact oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) (f₁.rel_dom hrel) hYne
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, hX'ne, -, rfl⟩ | ⟨Y, Y', hrel, -, hY'ne, -, rfl⟩)
    · exact Or.inl rfl
    · exact oplusTok_mem_embF (h₀ := B₀.ne) (h₁ := B₁.ne) (f₀.rel_cod hrel) hX'ne
    · exact oplusTok_mem_embT (h₀ := B₀.ne) (h₁ := B₁.ne) (f₁.rel_cod hrel) hY'ne
  master_rel := Or.inl ⟨(A₀.oplus A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, hWeq, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr (Or.inl ⟨X, X', hrel, hXne, hX'ne, hWeq,
          by rw [sumTokMaster_inter_embF (f₀.rel_cod hrel)]⟩)
      · exact Or.inr (Or.inr ⟨Y, Y', hrel, hYne, hY'ne, hWeq,
          by rw [sumTokMaster_inter_embT (f₁.rel_cod hrel)]⟩)
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hX₂ne, hX'₂ne, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, -, -, hWeq, rfl⟩
      · refine Or.inr (Or.inl ⟨X, X', hrel, hXne, hX'ne, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embF (f₀.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inl ⟨X, X' ∩ X'₂, f₀.inter_right hrel hrel₂, hXne,
          inter_ne_of_ne_left (B₀.sys.sub_master (f₀.rel_cod hrel)) hX'ne, rfl,
          embBit_inter false X' X'₂⟩)
      · exact absurd hWeq (embBit_ne (by decide) (A₀.ne X (f₀.rel_dom hrel)))
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, -, -, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hY₂ne, hY'₂ne, hWeq, rfl⟩
      · refine Or.inr (Or.inr ⟨Y, Y', hrel, hYne, hY'ne, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embT (f₁.rel_cod hrel)]
      · exact absurd hWeq (embBit_ne (by decide) (A₁.ne Y (f₁.rel_dom hrel)))
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inr ⟨Y, Y' ∩ Y'₂, f₁.inter_right hrel hrel₂, hYne,
          inter_ne_of_ne_left (B₁.sys.sub_master (f₁.rel_cod hrel)) hY'ne, rfl,
          embBit_inter true Y' Y'₂⟩)
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hW'' hZ'
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩
    · exact Or.inl ⟨hW'', Set.Subset.antisymm ((B₀.oplus B₁).sys.sub_master hZ') hZZ'⟩
    · rcases hZ' with rfl | ⟨X₃, hX₃, hX₃ne, rfl⟩ | ⟨Y₃, hY₃, hY₃ne, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · rcases hW'' with rfl | ⟨X₂, hX₂, hX₂ne, rfl⟩ | ⟨Y₂, hY₂, hY₂ne, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X₂, X₃,
            f₀.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃,
            hX₂ne, hX₃ne, rfl, rfl⟩)
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₁.ne Y₂ hY₂) hsub)
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₀.ne X' (f₀.rel_cod hrel)) hsub)
    · rcases hZ' with rfl | ⟨X₃, hX₃, hX₃ne, rfl⟩ | ⟨Y₃, hY₃, hY₃ne, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₁.ne Y' (f₁.rel_cod hrel)) hsub)
      · rcases hW'' with rfl | ⟨X₂, hX₂, hX₂ne, rfl⟩ | ⟨Y₂, hY₂, hY₂ne, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₀.ne X₂ hX₂) hsub)
        · exact Or.inr (Or.inr ⟨Y₂, Y₃,
            f₁.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hY₂ hY₃,
            hY₂ne, hY₃ne, rfl, rfl⟩)

/-! ## The functorial action of the smash product on (strict) maps

As `prodMapTok`, but proper rectangles require both components proper, and a **master/collapse row**
absorbs a boundary hit `f₀(X) = Δ₀'` (or `f₁(Y) = Δ₁'`) into the top `M`. -/

/-- **`f₀ ⊗ f₁`, the action of the smash product on maps.** -/
def otimesMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.otimes A₁).sys (B₀.otimes B₁).sys where
  rel W W' :=
    ((A₀.otimes A₁).sys.mem W ∧ W' = prodTokNbhd B₀.sys.master B₁.sys.master) ∨
    (∃ X Y X' Y', f₀.rel X X' ∧ f₁.rel Y Y' ∧ X ≠ A₀.sys.master ∧ Y ≠ A₁.sys.master ∧
      X' ≠ B₀.sys.master ∧ Y' ≠ B₁.sys.master ∧ W = prodTokNbhd X Y ∧ W' = prodTokNbhd X' Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, Y, X', Y', h0, h1, hXne, hYne, -, -, rfl, -⟩)
    · exact hW
    · exact otimesTok_mem_prod (f₀.rel_dom h0) (f₁.rel_dom h1) hXne hYne
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, Y, X', Y', h0, h1, -, -, hX'ne, hY'ne, -, rfl⟩)
    · exact otimesTok_mem_master
    · exact otimesTok_mem_prod (f₀.rel_cod h0) (f₁.rel_cod h1) hX'ne hY'ne
  master_rel := Or.inl ⟨(A₀.otimes A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · refine Or.inr ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, hWeq, ?_⟩
        rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (B₀.sys.sub_master (f₀.rel_cod hr0)),
          Set.inter_eq_right.mpr (B₁.sys.sub_master (f₁.rel_cod hr1))]
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, Y₂, X'₂, Y'₂, hr0₂, hr1₂, hX₂ne, hY₂ne, hX'₂ne, hY'₂ne, hWeq, rfl⟩
      · refine Or.inr ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, ?_⟩
        rw [Set.inter_comm, prodTokNbhd_inter,
          Set.inter_eq_right.mpr (B₀.sys.sub_master (f₀.rel_cod hr0)),
          Set.inter_eq_right.mpr (B₁.sys.sub_master (f₁.rel_cod hr1))]
      · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
        refine Or.inr ⟨X, Y, X' ∩ X'₂, Y' ∩ Y'₂, f₀.inter_right hr0 hr0₂,
          f₁.inter_right hr1 hr1₂, hXne, hYne,
          inter_ne_of_ne_left (B₀.sys.sub_master (f₀.rel_cod hr0)) hX'ne,
          inter_ne_of_ne_left (B₁.sys.sub_master (f₁.rel_cod hr1)) hY'ne, rfl, ?_⟩
        rw [prodTokNbhd_inter]
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hZmem hZ'mem
    rcases h with ⟨-, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · exact Or.inl ⟨hZmem, Set.Subset.antisymm ((B₀.otimes B₁).sys.sub_master hZ'mem) hZZ'⟩
    · rcases hZmem with rfl | ⟨Xz, Yz, hXz, hYz, hXzne, hYzne, rfl⟩
      · obtain ⟨hsubX, -⟩ := prodTokNbhd_subset_iff.mp hWW
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master (f₀.rel_dom hr0)) hsubX) hXne
      · rcases hZ'mem with rfl | ⟨Xz', Yz', hXz', hYz', hXz'ne, hYz'ne, rfl⟩
        · exact Or.inl ⟨otimesTok_mem_prod hXz hYz hXzne hYzne, rfl⟩
        · obtain ⟨hXzX, hYzY⟩ := prodTokNbhd_subset_iff.mp hWW
          obtain ⟨hX'Xz', hY'Yz'⟩ := prodTokNbhd_subset_iff.mp hZZ'
          exact Or.inr ⟨Xz, Yz, Xz', Yz', f₀.mono hr0 hXzX hX'Xz' hXz hXz',
            f₁.mono hr1 hYzY hY'Yz' hYz hYz', hXzne, hYzne, hXz'ne, hYz'ne, rfl, rfl⟩

/-! ## The extended functor-expression algebra `GExpr`

Scott's *"do the same as 6.19 and 6.20 when the functors are also allowed to be generated by the
operations `⊕`, `⊗`"*: the closed family of constructs is enlarged from `FExpr` (constants,
identity, `+`, `×`) to also include the coalesced `⊕` and the smash `⊗`. The functor laws and the
on-maps/on-domains continuity properties are re-established by induction; the `⊕`/`⊗` composition
law carries the strictness hypothesis (Scott's category is the **strict-map** category, and that is
exactly what makes `⊕`/`⊗` functorial). -/

/-- **The action of `T` on objects.** -/
def GExpr.obj : GExpr → ScottSys → ScottSys
  | .const D, _ => D
  | .var, X => X
  | .sum a b, X => (a.obj X).sum (b.obj X)
  | .prod a b, X => (a.obj X).prod (b.obj X)
  | .oplus a b, X => (a.obj X).oplus (b.obj X)
  | .otimes a b, X => (a.obj X).otimes (b.obj X)

/-- **The action of `T` on maps.** -/
def GExpr.map : (T : GExpr) → {X Y : ScottSys} → ApproximableMap X.sys Y.sys →
    ApproximableMap (T.obj X).sys (T.obj Y).sys
  | .const D, _, _, _ => idMap D.sys
  | .var, _, _, f => f
  | .sum a b, _, _, f => sumMapTok (a.map f) (b.map f)
  | .prod a b, _, _, f => prodMapTok (a.map f) (b.map f)
  | .oplus a b, _, _, f => oplusMapTok (a.map f) (b.map f)
  | .otimes a b, _, _, f => otimesMapTok (a.map f) (b.map f)

/-! ### Continuous on domains -/

/-! ### Continuous on maps -/

/-! ## Exercise 6.20 for the extended algebra — `λΓ. tok(T({Γ}))` is continuous, so a fixed point
exists

The masters of `⊕`/`⊗` coincide with those of `+`/`×` (all four equal `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`), so the
token-level recursion `gFun` has the **same** tagged-union body in all four binary cases. The 6.20
argument (continuity of `λΓ. tok(T({Γ}))` and existence of `Γ = tok(T({Γ}))`, whence
`{Γ} ◁ T({Γ})` and Theorem 6.14 applies) goes through verbatim, reusing the generic helpers
`singletonSys`, `insertTag_mono`, `insertTag_continuous` of Exercise 6.19 Part B. -/

/-- **The token-level master recursion for `GExpr`.** All four binary operations share the same body
(`sumTokMaster = prodTokNbhd` on masters). -/
def gFun : GExpr → Set Str → Set Str
  | .const C, _ => C.sys.master
  | .var, Γ => Γ
  | .sum a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .prod a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .oplus a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .otimes a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))

/-- `gFun T Γ = tok(T({Γ}))`. -/
theorem gFun_eq_master : (T : GExpr) → {Γ : Set Str} → (h : Γ.Nonempty) →
    gFun T Γ = (T.obj (singletonSys Γ h)).sys.master
  | .const _, _, _ => rfl
  | .var, _, _ => rfl
  | .sum a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .prod a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .oplus a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .otimes a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]

/-- **`λΓ. tok(T({Γ}))` is monotone.** -/
theorem gFun_mono (T : GExpr) {Γ Γ' : Set Str} (h : Γ ⊆ Γ') : gFun T Γ ⊆ gFun T Γ' := by
  induction T with
  | const C => exact subset_rfl
  | var => exact h
  | sum a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | prod a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | oplus a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | otimes a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁

/-- **`λΓ. tok(T({Γ}))` is continuous on `{Γ ∣ Λ ∈ Γ}`.** -/
theorem gFun_continuous (T : GExpr) {ℱ : Set (Set Str)} {U : Set Str}
    (_hdir : DirectedOn (· ⊆ ·) ℱ) (hne : ℱ.Nonempty)
    (hU : ∀ w, w ∈ U ↔ ∃ Γ ∈ ℱ, w ∈ Γ) :
    ∀ w, w ∈ gFun T U ↔ ∃ Γ ∈ ℱ, w ∈ gFun T Γ := by
  induction T with
  | const C =>
      intro w
      exact ⟨fun hw => let ⟨Γ, hΓ⟩ := hne; ⟨Γ, hΓ, hw⟩, fun ⟨_, _, hw⟩ => hw⟩
  | var => intro w; exact hU w
  | sum a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | prod a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | oplus a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | otimes a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w

/-- **`Λ ∈ tok(C)` for every constant `C` occurring in `T`.** -/
def GExpr.RootedConst : GExpr → Prop
  | .const C => ([] : Str) ∈ C.sys.master
  | .var => True
  | .sum a b => a.RootedConst ∧ b.RootedConst
  | .prod a b => a.RootedConst ∧ b.RootedConst
  | .oplus a b => a.RootedConst ∧ b.RootedConst
  | .otimes a b => a.RootedConst ∧ b.RootedConst

theorem gFun_nil_mem : ∀ (T : GExpr), T.RootedConst → {Γ : Set Str} →
    ([] : Str) ∈ Γ → ([] : Str) ∈ gFun T Γ
  | .const _, hC, _, _ => hC
  | .var, _, _, hΓ => hΓ
  | .sum _ _, _, _, _ => Set.mem_insert _ _
  | .prod _ _, _, _, _ => Set.mem_insert _ _
  | .oplus _ _, _, _, _ => Set.mem_insert _ _
  | .otimes _ _, _, _, _ => Set.mem_insert _ _

/-- The **Kleene iteration** `gFunⁿ({Λ})`. -/
def gIter (T : GExpr) : ℕ → Set Str
  | 0 => {([] : Str)}
  | n + 1 => gFun T (gIter T n)

theorem nil_mem_gIter (T : GExpr) (hT : T.RootedConst) : ∀ n, ([] : Str) ∈ gIter T n
  | 0 => rfl
  | n + 1 => gFun_nil_mem T hT (nil_mem_gIter T hT n)

theorem gIter_mono_step (T : GExpr) (hT : T.RootedConst) :
    ∀ n, gIter T n ⊆ gIter T (n + 1)
  | 0 => by
      intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact gFun_nil_mem T hT rfl
  | n + 1 => gFun_mono T (gIter_mono_step T hT n)

theorem gIter_mono (T : GExpr) (hT : T.RootedConst) {m n : ℕ} (hmn : m ≤ n) :
    gIter T m ⊆ gIter T n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => intro x hx; exact gIter_mono_step T hT _ (ih hx)

/-- The Kleene union is a **fixed point** of `λΓ. tok(T({Γ}))`. -/
theorem gFun_iter_fixed (T : GExpr) (hT : T.RootedConst) :
    gFun T (⋃ n, gIter T n) = ⋃ n, gIter T n := by
  have hstep := gIter_mono_step T hT
  have hne : (Set.range (gIter T)).Nonempty := ⟨gIter T 0, 0, rfl⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range (gIter T)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨gIter T (max i j), ⟨max i j, rfl⟩,
      gIter_mono T hT (le_max_left i j), gIter_mono T hT (le_max_right i j)⟩
  have hU : ∀ v, v ∈ (⋃ n, gIter T n) ↔ ∃ S ∈ Set.range (gIter T), v ∈ S := by
    intro v
    constructor
    · intro hv; rw [Set.mem_iUnion] at hv; obtain ⟨n, hn⟩ := hv
      exact ⟨gIter T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨S, ⟨n, rfl⟩, hv⟩; exact Set.mem_iUnion.mpr ⟨n, hv⟩
  apply Set.ext; intro w
  rw [gFun_continuous T hdir hne hU w]
  constructor
  · rintro ⟨S, ⟨n, rfl⟩, hwS⟩; exact Set.mem_iUnion.mpr ⟨n + 1, hwS⟩
  · intro hw
    rw [Set.mem_iUnion] at hw; obtain ⟨n, hn⟩ := hw
    exact ⟨gIter T n, ⟨n, rfl⟩, hstep n hn⟩

/-- **Exercise 6.21/6.20 (token level).** For any `GExpr` `T` whose constants contain `Λ`, there is a
set `Γ` with `Λ ∈ Γ` and `Γ = tok(T({Γ}))`. -/
theorem gExists_tok_fixedPoint (T : GExpr) (hT : T.RootedConst) :
    ∃ Γ : Set Str, ([] : Str) ∈ Γ ∧ gFun T Γ = Γ :=
  ⟨⋃ n, gIter T n, Set.mem_iUnion.mpr ⟨0, nil_mem_gIter T hT 0⟩, gFun_iter_fixed T hT⟩

/-- **Exercise 6.21/6.20 (object level): `{Γ} ◁ T({Γ})`, so Theorem 6.14 applies** for any construct
`T` built from constants, identity, `+`, `×`, `⊕`, `⊗`. -/
theorem gExists_singleton_subsystem (T : GExpr) (hT : T.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ, hnil, hfix⟩ := gExists_tok_fixedPoint T hT
  have hne : Γ.Nonempty := ⟨[], hnil⟩
  have hmaster : (T.obj (singletonSys Γ hne)).sys.master = Γ :=
    (gFun_eq_master T hne).symm.trans hfix
  refine ⟨Γ, hne, ?_, ?_, ?_⟩
  · exact hmaster.symm
  · intro X hX
    have heq : X = (T.obj (singletonSys Γ hne)).sys.master := (hX : X = Γ).trans hmaster.symm
    rw [heq]
    exact (T.obj (singletonSys Γ hne)).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = Γ
    rw [show X = Γ from hX, show Y = Γ from hY, Set.inter_self]

/-! ## Generalizing `+`, `×`, `⊕`, `⊗` to combinations of several terms

> Generalize all of `+`, `×`, `⊕`, `⊗` to combinations of several terms, not just the binary sums
> and products.

Because `GExpr` is **closed** under the binary operations, every finite combination of several terms
`T₀ ⋆ T₁ ⋆ ⋯ ⋆ Tₙ` (for any `⋆ ∈ {+, ×, ⊕, ⊗}`, in any nesting) is itself a `GExpr` — so the
results already proved (`map_id`, `map_comp`, `map_mono`, `map_continuous`, `obj_subsystem`,
`obj_continuous`, and the 6.20 fixed point `gExists_singleton_subsystem`) apply to *all* of them with
no further work. The `naryOp` fold below packages the common right-nested n-ary constructs
`⋆(a, [b, c, …]) = a ⋆ (b ⋆ (c ⋆ ⋯))` explicitly, and `naryOp_rootedConst` shows the `Λ ∈ tok`
side-condition (needed for the 6.20 fixed point) is preserved, so every n-ary construct also has a
solution `Γ = tok(T({Γ}))`. -/

/-- **Right-nested n-ary fold** of a binary construct-operation `op` over a non-empty list `a, l…`.
With `op = .sum`/`.prod`/`.oplus`/`.otimes` this is the n-ary `+`/`×`/`⊕`/`⊗`. -/
def GExpr.naryOp (op : GExpr → GExpr → GExpr) (a : GExpr) : List GExpr → GExpr
  | [] => a
  | b :: l => op a (GExpr.naryOp op b l)

/-- n-ary separated sum `T₀ + T₁ + ⋯ + Tₙ`. -/
def GExpr.narySum : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.sum

/-- n-ary separated product `T₀ × T₁ × ⋯ × Tₙ`. -/
def GExpr.naryProd : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.prod

/-- n-ary coalesced sum `T₀ ⊕ T₁ ⊕ ⋯ ⊕ Tₙ`. -/
def GExpr.naryOplus : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.oplus

/-- n-ary smash product `T₀ ⊗ T₁ ⊗ ⋯ ⊗ Tₙ`. -/
def GExpr.naryOtimes : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.otimes
end Exercise619
end DomainTheory.NeighbourhoodSystems
