module
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_1

public import Mathlib.Data.Set.Operations
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem
variable {α β γ δ : Type*}

def prodNbhd (X : Set α) (Y : Set β) : Set (α ⊕ β) := Sum.inl '' X ∪ Sum.inr '' Y

@[simp] theorem mem_prodNbhd_inl {X : Set α} {Y : Set β} {a : α} :
    (Sum.inl a : α ⊕ β) ∈ prodNbhd X Y ↔ a ∈ X := by
  simp [prodNbhd]

@[simp] theorem mem_prodNbhd_inr {X : Set α} {Y : Set β} {b : β} :
    (Sum.inr b : α ⊕ β) ∈ prodNbhd X Y ↔ b ∈ Y := by
  simp [prodNbhd]

@[simp] theorem inl_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inl ⁻¹' prodNbhd X Y = X := by ext a; simp

@[simp] theorem inr_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inr ⁻¹' prodNbhd X Y = Y := by ext b; simp

theorem prodNbhd_injective {X X' : Set α} {Y Y' : Set β}
    (h : prodNbhd X Y = prodNbhd X' Y') : X = X' ∧ Y = Y' := by
  refine ⟨?_, ?_⟩
  · rw [← inl_preimage_prodNbhd X Y, ← inl_preimage_prodNbhd X' Y', h]
  · rw [← inr_preimage_prodNbhd X Y, ← inr_preimage_prodNbhd X' Y', h]

theorem prodNbhd_inter (X X' : Set α) (Y Y' : Set β) :
    prodNbhd X Y ∩ prodNbhd X' Y' = prodNbhd (X ∩ X') (Y ∩ Y') := by
  ext (a | b) <;> simp [Set.mem_inter_iff]

theorem prodNbhd_subset_iff {X X' : Set α} {Y Y' : Set β} :
    prodNbhd X Y ⊆ prodNbhd X' Y' ↔ X ⊆ X' ∧ Y ⊆ Y' := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have : (Sum.inl a : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using ha)
      simpa using this
    · have : (Sum.inr b : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using hb)
      simpa using this
  · rintro ⟨hX, hY⟩ (a | b) hs
    · simp only [mem_prodNbhd_inl] at hs ⊢; exact hX hs
    · simp only [mem_prodNbhd_inr] at hs ⊢; exact hY hs

def prod (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : NeighborhoodSystem (α ⊕ β) where
  mem W := ∃ X Y, V₀.mem X ∧ V₁.mem Y ∧ W = prodNbhd X Y
  master := prodNbhd V₀.master V₁.master
  master_nonempty := by
    obtain ⟨a, ha⟩ := V₀.master_nonempty
    exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩
  master_mem := ⟨V₀.master, V₁.master, V₀.master_mem, V₁.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ ⟨Z₀, Z₁, hZ₀, hZ₁, rfl⟩ hsub
    rw [prodNbhd_inter] at hsub ⊢
    obtain ⟨hsub₀, hsub₁⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X ∩ X', Y ∩ Y', V₀.inter_mem hX hX' hZ₀ hsub₀, V₁.inter_mem hY hY' hZ₁ hsub₁, rfl⟩
  sub_master := by
    rintro W ⟨X, Y, hX, hY, rfl⟩
    exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩
end

section
open NeighborhoodSystem
variable {α β γ δ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem prod_mem_iff {W : Set (α ⊕ β)} :
    (prod V₀ V₁).mem W ↔ ∃ X Y, V₀.mem X ∧ V₁.mem Y ∧ W = prodNbhd X Y := Iff.rfl

@[simp] theorem prod_master : (prod V₀ V₁).master = prodNbhd V₀.master V₁.master := rfl

theorem prod_mem_prodNbhd {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (prod V₀ V₁).mem (prodNbhd X Y) := ⟨X, Y, hX, hY, rfl⟩

theorem prod_mem_prodNbhd_iff {X : Set α} {Y : Set β} :
    (prod V₀ V₁).mem (prodNbhd X Y) ↔ V₀.mem X ∧ V₁.mem Y := by
  constructor
  · rintro ⟨A, B, hA, hB, heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hA, hB⟩
  · rintro ⟨hX, hY⟩; exact prod_mem_prodNbhd hX hY

theorem prodNbhd_preimage {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) :
    W = prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W) := by
  obtain ⟨X, Y, _, _, rfl⟩ := hW
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]

def NeighborhoodSystem.Element.fst (z : (prod V₀ V₁).Element) : V₀.Element where
  mem X := V₀.mem X ∧ z.mem (prodNbhd X V₁.master)
  sub h := h.1
  master_mem := ⟨V₀.master_mem, z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz := z.inter_mem hzX hzX'
    rw [prodNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, hA, _, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hA, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    refine ⟨hX', z.up_mem hzX (prod_mem_prodNbhd hX' V₁.master_mem) ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩

@[simp] theorem mem_fst {z : (prod V₀ V₁).Element} {X : Set α} :
    z.fst.mem X ↔ V₀.mem X ∧ z.mem (prodNbhd X V₁.master) := Iff.rfl

def NeighborhoodSystem.Element.snd (z : (prod V₀ V₁).Element) : V₁.Element where
  mem Y := V₁.mem Y ∧ z.mem (prodNbhd V₀.master Y)
  sub h := h.1
  master_mem := ⟨V₁.master_mem, z.master_mem⟩
  inter_mem := by
    rintro Y Y' ⟨_, hzY⟩ ⟨_, hzY'⟩
    have hz := z.inter_mem hzY hzY'
    rw [prodNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, _, hB, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hB, hz⟩
  up_mem := by
    rintro Y Y' ⟨_, hzY⟩ hY' hYY'
    refine ⟨hY', z.up_mem hzY (prod_mem_prodNbhd V₀.master_mem hY') ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨subset_rfl, hYY'⟩

@[simp] theorem mem_snd {z : (prod V₀ V₁).Element} {Y : Set β} :
    z.snd.mem Y ↔ V₁.mem Y ∧ z.mem (prodNbhd V₀.master Y) := Iff.rfl

def pair (x : V₀.Element) (y : V₁.Element) : (prod V₀ V₁).Element where
  mem W := ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodNbhd X Y
  sub := by rintro W ⟨X, Y, hX, hY, rfl⟩; exact prod_mem_prodNbhd (x.sub hX) (y.sub hY)
  master_mem := ⟨V₀.master, V₁.master, x.master_mem, y.master_mem, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩
    exact ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', y.inter_mem hY hY', prodNbhd_inter X X' Y Y'⟩
  up_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hsub
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', x.up_mem hX hX' hXX', y.up_mem hY hY' hYY', rfl⟩

@[simp] theorem mem_pair {x : V₀.Element} {y : V₁.Element} {W : Set (α ⊕ β)} :
    (pair x y).mem W ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodNbhd X Y := Iff.rfl

theorem mem_pair_prodNbhd {x : V₀.Element} {y : V₁.Element} {X : Set α} {Y : Set β} :
    (pair x y).mem (prodNbhd X Y) ↔ x.mem X ∧ y.mem Y := by
  constructor
  · rintro ⟨X', Y', hX', hY', heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hX', hY'⟩
  · rintro ⟨hx, hy⟩; exact ⟨X, Y, hx, hy, rfl⟩

@[simp] theorem fst_pair (x : V₀.Element) (y : V₁.Element) : (pair x y).fst = x := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hX, hmem⟩
    exact (mem_pair_prodNbhd.mp hmem).1
  · intro hX
    exact ⟨x.sub hX, mem_pair_prodNbhd.mpr ⟨hX, y.master_mem⟩⟩

theorem prod_mem_split {z : (prod V₀ V₁).Element} {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    z.mem (prodNbhd X Y) ↔ z.mem (prodNbhd X V₁.master) ∧ z.mem (prodNbhd V₀.master Y) := by
  constructor
  · intro h
    refine ⟨z.up_mem h (prod_mem_prodNbhd hX V₁.master_mem) ?_,
            z.up_mem h (prod_mem_prodNbhd V₀.master_mem hY) ?_⟩
    · exact prodNbhd_subset_iff.mpr ⟨subset_rfl, V₁.sub_master hY⟩
    · exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, subset_rfl⟩
  · rintro ⟨h1, h2⟩
    have := z.inter_mem h1 h2
    rwa [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master hX),
      Set.inter_eq_right.mpr (V₁.sub_master hY)] at this

theorem pair_fst_snd (z : (prod V₀ V₁).Element) : pair z.fst z.snd = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, Y, ⟨hX, hzX⟩, ⟨hY, hzY⟩, rfl⟩
    exact (prod_mem_split hX hY).mpr ⟨hzX, hzY⟩
  · intro hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
    obtain ⟨h1, h2⟩ := (prod_mem_split hX hY).mp hW
    exact ⟨X, Y, ⟨hX, h1⟩, ⟨hY, h2⟩, rfl⟩

@[simp] theorem snd_pair (x : V₀.Element) (y : V₁.Element) : (pair x y).snd = y := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, hmem⟩
    exact (mem_pair_prodNbhd.mp hmem).2
  · intro hY
    exact ⟨y.sub hY, mem_pair_prodNbhd.mpr ⟨x.master_mem, hY⟩⟩

theorem prod_mem_inl {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) : V₀.mem (Sum.inl ⁻¹' W) := by
  obtain ⟨X, Y, hX, _, rfl⟩ := hW; rwa [inl_preimage_prodNbhd]

theorem prod_mem_inr {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) : V₁.mem (Sum.inr ⁻¹' W) := by
  obtain ⟨X, Y, _, hY, rfl⟩ := hW; rwa [inr_preimage_prodNbhd]

end
end DomainTheory.NeighbourhoodSystems
end
