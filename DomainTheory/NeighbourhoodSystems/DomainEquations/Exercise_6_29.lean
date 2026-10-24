module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_4
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_7
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_21
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_16
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem_5_6
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_7
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_22
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_19

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem
namespace Exercise629
universe u v
variable {ι : Type u} {α : ι → Type v}
variable {D : ∀ i, NeighborhoodSystem (α i)}
section IndexedProduct
variable [Nonempty ι]
variable (D) in
/- concordance: source L4215 EXERCISE 6.29 infinitary sum and product -/
/-- **Exercise 6.29 — the indexed product `∏_i D_i`.** The index type is non-empty so the
dependent-sum token set contains a token. Neighbourhoods are cylinders: tuples `X i ∈ 𝒟ᵢ`
that are the master in all but finitely many coordinates. -/
def iprod : NeighborhoodSystem (Σ i, α i) where
  mem W := ∃ X : ∀ i, Set (α i), (∀ i, (D i).mem (X i)) ∧ FinSupp D X ∧ W = iprodNbhd X
  master := iprodNbhd (fun i => (D i).master)
  master_nonempty := by
    cases ‹Nonempty ι› with
    | intro i =>
      obtain ⟨a, ha⟩ := (D i).master_nonempty
      exact ⟨⟨i, a⟩, ha⟩
  master_mem := ⟨fun i => (D i).master, fun i => (D i).master_mem, FinSupp.master, rfl⟩
  sub_master := by
    rintro W ⟨X, hX, _, rfl⟩
    exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i)
  inter_mem := by
    rintro W W' Z ⟨X, hX, hXf, rfl⟩ ⟨X', hX', hX'f, rfl⟩ ⟨ZZ, hZZ, _, rfl⟩ hsub
    rw [iprodNbhd_inter] at hsub ⊢
    refine ⟨fun i => X i ∩ X' i, fun i => ?_, hXf.inter hX'f, rfl⟩
    have : ZZ i ⊆ X i ∩ X' i := iprodNbhd_subset_iff.mp hsub i
    exact (D i).inter_mem (hX i) (hX' i) (hZZ i) this

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]

section Iso

variable [DecidableEq ι]

/-- The tuple that is `U` at coordinate `i` and the master elsewhere. -/
def updTuple (D : ∀ i, NeighborhoodSystem (α i)) (i : ι) (U : Set (α i)) : ∀ j, Set (α j) :=
  Function.update (fun j => (D j).master) i U

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
@[simp] theorem updTuple_apply_self (i : ι) (U : Set (α i)) : updTuple D i U i = U := by
  simp [updTuple]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- **The element of `∏_i D_i` assembled from a tuple of components.** -/
def fromPi (D : ∀ i, NeighborhoodSystem (α i)) (x : ∀ i, (D i).Element) : (iprod D).Element where
  mem W := ∃ X : ∀ i, Set (α i), (∀ i, (x i).mem (X i)) ∧ FinSupp D X ∧ W = iprodNbhd X
  sub := by rintro W ⟨X, hX, hXf, rfl⟩; exact ⟨X, fun i => (x i).sub (hX i), hXf, rfl⟩
  master_mem := ⟨fun i => (D i).master, fun i => (x i).master_mem, FinSupp.master, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, hX, hXf, rfl⟩ ⟨X', hX', hX'f, rfl⟩
    exact ⟨fun i => X i ∩ X' i, fun i => (x i).inter_mem (hX i) (hX' i), hXf.inter hX'f,
      iprodNbhd_inter X X'⟩
  up_mem := by
    rintro W W' ⟨X, hX, _, rfl⟩ hW' hsub
    obtain ⟨X', hX'mem, hX'f, rfl⟩ := hW'
    rw [iprodNbhd_subset_iff] at hsub
    exact ⟨X', fun i => (x i).up_mem (hX i) (hX'mem i) (hsub i), hX'f, rfl⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- A tagged copy `inj i X = {some ⟨i, a⟩ ∣ a ∈ X}` of summand `i`. -/
def injI (i : ι) (X : Set (α i)) : Set (Option (Σ i, α i)) :=
  (fun a => (some ⟨i, a⟩ : Option (Σ i, α i))) '' X

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem none_not_mem_injI {i : ι} {X : Set (α i)} : (none : Option (Σ i, α i)) ∉ injI i X := by
  rintro ⟨a, _, heq⟩; simp at heq

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- The cylinder restricted to a list of coordinates `l` (master outside `l`). -/
def restrictTo (D : ∀ i, NeighborhoodSystem (α i)) (l : List ι) (X : ∀ i, Set (α i)) :
    ∀ j, Set (α j) := fun j => if j ∈ l then X j else (D j).master

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- The slice cylinder: `U` at coordinate `i`, master elsewhere. -/
def slice (D : ∀ i, NeighborhoodSystem (α i)) (i : ι) (U : Set (α i)) : Set (Σ i, α i) :=
  iprodNbhd (updTuple D i U)

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- Recovering the coordinate from a slice neighbourhood. -/
theorem iprod_mem_slice_inv {i : ι} {U : Set (α i)} (h : (iprod D).mem (slice D i U)) :
    (D i).mem U := by
  obtain ⟨X, hX, _, heq⟩ := h
  have hXeq : updTuple D i U = X := iprodNbhd_injective heq
  have hi := hX i
  rwa [← hXeq, updTuple_apply_self] at hi

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
theorem slice_eq (i : ι) (U : Set (α i)) : slice D i U = iprodNbhd (updTuple D i U) := rfl

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

@[simp] theorem some_mem_injI {i : ι} {a : α i} {X : Set (α i)} :
    (some ⟨i, a⟩ : Option (Σ i, α i)) ∈ injI i X ↔ a ∈ X := by
  constructor
  · rintro ⟨b, hb, heq⟩
    simp only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at heq
    rwa [heq] at hb
  · intro ha; exact ⟨a, ha, rfl⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- A tagged token determines its summand index. -/
theorem index_of_some_mem_injI {i k : ι} {a : α k} {X : Set (α i)}
    (hmem : (some ⟨k, a⟩ : Option (Σ i, α i)) ∈ injI i X) : k = i := by
  obtain ⟨b, _, heq⟩ := hmem
  simp only [Option.some.injEq] at heq
  exact (congrArg Sigma.fst heq).symm

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem injI_inter_same (i : ι) (X Y : Set (α i)) : injI i X ∩ injI i Y = injI i (X ∩ Y) := by
  apply Set.ext
  rintro (_ | ⟨k, a⟩)
  · constructor
    · rintro ⟨h, _⟩; exact absurd h none_not_mem_injI
    · intro h; exact absurd h none_not_mem_injI
  · constructor
    · rintro ⟨hx, hy⟩
      obtain rfl := index_of_some_mem_injI hx
      exact some_mem_injI.mpr ⟨some_mem_injI.mp hx, some_mem_injI.mp hy⟩
    · intro h
      obtain rfl := index_of_some_mem_injI h
      have h' := some_mem_injI.mp h
      exact ⟨some_mem_injI.mpr h'.1, some_mem_injI.mpr h'.2⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem injI_subset_iff {i : ι} {X Y : Set (α i)} : injI i X ⊆ injI i Y ↔ X ⊆ Y := by
  constructor
  · intro h a ha; exact some_mem_injI.mp (h (some_mem_injI.mpr ha))
  · intro h; rintro w ⟨a, ha, rfl⟩; exact ⟨a, h ha, rfl⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Exercise 6.29 — the indexed smash product `⊗_i D_i`.** The index type is non-empty so its
dependent-sum token set is non-empty. A proper neighbourhood is a cylinder proper in *every*
coordinate; closure under intersection is as for `iprod` plus the observation that
`X i ∩ X' i ⊆ X i ≠` master stays proper. -/
def iotimes [Nonempty ι] (D : ∀ i, NeighborhoodSystem (α i)) : NeighborhoodSystem (Σ i, α i) where
  mem W := W = iprodNbhd (fun i => (D i).master) ∨
    ∃ X : ∀ i, Set (α i), (∀ i, (D i).mem (X i)) ∧ (∀ i, X i ≠ (D i).master) ∧
      FinSupp D X ∧ W = iprodNbhd X
  master := iprodNbhd (fun i => (D i).master)
  master_nonempty := by
    cases ‹Nonempty ι› with
    | intro i =>
      obtain ⟨a, ha⟩ := (D i).master_nonempty
      exact ⟨⟨i, a⟩, ha⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, _, _, rfl⟩)
    · exact subset_rfl
    · exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i)
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨X, hX, hXne, hXf, rfl⟩
    · have hW'sub : W' ⊆ iprodNbhd (fun i => (D i).master) := by
        rcases hW' with rfl | ⟨X', hX', _, _, rfl⟩
        · exact subset_rfl
        · exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX' i)
      rw [Set.inter_eq_right.mpr hW'sub]; exact hW'
    · rcases hW' with rfl | ⟨X', hX', hX'ne, hX'f, rfl⟩
      · rw [Set.inter_eq_left.mpr (iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i))]
        exact Or.inr ⟨X, hX, hXne, hXf, rfl⟩
      · rw [iprodNbhd_inter] at hsub ⊢
        obtain ⟨ZZ, hZZmem, rfl⟩ : ∃ ZZ, (∀ i, (D i).mem (ZZ i)) ∧ Z = iprodNbhd ZZ := by
          rcases hZ with rfl | ⟨ZZ, hZZ, _, _, rfl⟩
          · exact ⟨fun i => (D i).master, fun i => (D i).master_mem, rfl⟩
          · exact ⟨ZZ, hZZ, rfl⟩
        refine Or.inr ⟨fun i => X i ∩ X' i, fun i => ?_, fun i => ?_, ?_, rfl⟩
        · exact (D i).inter_mem (hX i) (hX' i) (hZZmem i) (iprodNbhd_subset_iff.mp hsub i)
        · intro heq
          exact hXne i (Set.Subset.antisymm ((D i).sub_master (hX i))
            (by rw [← heq]; exact Set.inter_subset_left))
        · exact hXf.inter hX'f

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- The basepoint master of the indexed sum: `{none} ∪ {some ⟨i, a⟩ ∣ a ∈ Δᵢ}`. -/
def sumMasterI (D : ∀ i, NeighborhoodSystem (α i)) : Set (Option (Σ i, α i)) :=
  insert none ((fun p => (some p : Option (Σ i, α i))) '' iprodNbhd (fun i => (D i).master))

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem injI_subset_sumMasterI {i : ι} {X : Set (α i)} (hX : (D i).mem X) :
    injI i X ⊆ sumMasterI D := by
  rintro w ⟨a, ha, rfl⟩
  exact Set.mem_insert_iff.mpr (Or.inr ⟨⟨i, a⟩, (D i).sub_master hX ha, rfl⟩)

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem none_mem_sumMasterI : (none : Option (Σ i, α i)) ∈ sumMasterI D := Set.mem_insert _ _

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Exercise 6.29 — the indexed coalesced sum `⊕_i D_i`.** -/
def ioplus (D : ∀ i, NeighborhoodSystem (α i))
    (hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty) :
    NeighborhoodSystem (Option (Σ i, α i)) where
  mem W := W = sumMasterI D ∨ ∃ i, ∃ X : Set (α i), (D i).mem X ∧ X ≠ (D i).master ∧ W = injI i X
  master := sumMasterI D
  master_nonempty := ⟨none, none_mem_sumMasterI⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨i, X, hX, _, rfl⟩)
    · exact subset_rfl
    · exact injI_subset_sumMasterI hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨i, X, hX, hXne, rfl⟩
    · have hsub' : W' ⊆ sumMasterI D := by
        rcases hW' with rfl | ⟨j, Y, hY, _, rfl⟩
        · exact subset_rfl
        · exact injI_subset_sumMasterI hY
      rw [Set.inter_eq_right.mpr hsub']; exact hW'
    · rcases hW' with rfl | ⟨j, Y, hY, hYne, rfl⟩
      · rw [Set.inter_eq_left.mpr (injI_subset_sumMasterI hX)]
        exact Or.inr ⟨i, X, hX, hXne, rfl⟩
      · rcases hZ with rfl | ⟨k, Wk, hWk, _, rfl⟩
        · exact absurd (hsub none_mem_sumMasterI).1 none_not_mem_injI
        · obtain ⟨w, hw⟩ := hne k Wk hWk
          have hmemZ := hsub (some_mem_injI.mpr hw)
          obtain rfl := index_of_some_mem_injI hmemZ.1
          obtain rfl := index_of_some_mem_injI hmemZ.2
          rw [injI_inter_same] at hsub ⊢
          exact Or.inr ⟨k, X ∩ Y, (D k).inter_mem hX hY hWk (injI_subset_iff.mp hsub),
            fun heq => hXne (Set.Subset.antisymm ((D k).sub_master hX)
              (heq ▸ Set.inter_subset_left)), rfl⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Exercise 6.29 — the indexed separated sum `∑_i D_i`.** -/
def isum (D : ∀ i, NeighborhoodSystem (α i))
    (hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty) :
    NeighborhoodSystem (Option (Σ i, α i)) where
  mem W := W = sumMasterI D ∨ ∃ i, ∃ X : Set (α i), (D i).mem X ∧ W = injI i X
  master := sumMasterI D
  master_nonempty := ⟨none, none_mem_sumMasterI⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨i, X, hX, rfl⟩)
    · exact subset_rfl
    · exact injI_subset_sumMasterI hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨i, X, hX, rfl⟩
    · have hsub' : W' ⊆ sumMasterI D := by
        rcases hW' with rfl | ⟨j, Y, hY, rfl⟩
        · exact subset_rfl
        · exact injI_subset_sumMasterI hY
      rw [Set.inter_eq_right.mpr hsub']; exact hW'
    · rcases hW' with rfl | ⟨j, Y, hY, rfl⟩
      · rw [Set.inter_eq_left.mpr (injI_subset_sumMasterI hX)]
        exact Or.inr ⟨i, X, hX, rfl⟩
      · -- both proper: the consistency witness `Z` forces `i = j` constructively.
        rcases hZ with rfl | ⟨k, Wk, hWk, rfl⟩
        · exact absurd (hsub none_mem_sumMasterI).1 none_not_mem_injI
        · obtain ⟨w, hw⟩ := hne k Wk hWk
          have hmemZ := hsub (some_mem_injI.mpr hw)
          obtain rfl := index_of_some_mem_injI hmemZ.1
          obtain rfl := index_of_some_mem_injI hmemZ.2
          rw [injI_inter_same] at hsub ⊢
          exact Or.inr ⟨k, X ∩ Y, (D k).inter_mem hX hY hWk (injI_subset_iff.mp hsub), rfl⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
theorem updTuple_apply_ne {i j : ι} (U : Set (α i)) (h : j ≠ i) :
    updTuple D i U j = (D j).master := by
  simp [updTuple, Function.update_of_ne h]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

theorem fromPi_mem_slice (x : ∀ i, (D i).Element) (i : ι) (U : Set (α i)) :
    (fromPi D x).mem (slice D i U) ↔ (x i).mem U := by
  constructor
  · rintro ⟨X, hX, _, heq⟩
    have hXeq : updTuple D i U = X := iprodNbhd_injective heq
    have hi := hX i
    rwa [← hXeq, updTuple_apply_self] at hi
  · intro hU
    refine ⟨updTuple D i U, fun j => ?_, ⟨[i], fun j hj => ?_⟩, rfl⟩
    · by_cases h : j = i
      · subst h; rw [updTuple_apply_self]; exact hU
      · rw [updTuple_apply_ne U h]; exact (x j).master_mem
    · exact updTuple_apply_ne U fun h => hj (List.mem_singleton.mpr h)

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
theorem iprodNbhd_restrictTo_cons {X : ∀ i, Set (α i)} (hXsub : ∀ i, X i ⊆ (D i).master)
    (a : ι) (l : List ι) :
    iprodNbhd (restrictTo D (a :: l) X) = slice D a (X a) ∩ iprodNbhd (restrictTo D l X) := by
  rw [slice_eq, iprodNbhd_inter]
  congr 1; funext j
  show (if j ∈ a :: l then X j else (D j).master)
      = updTuple D a (X a) j ∩ (if j ∈ l then X j else (D j).master)
  by_cases hja : j = a
  · subst hja
    rw [updTuple_apply_self]
    by_cases hjl : j ∈ l
    · rw [ite_eq_left List.mem_cons_self, ite_eq_left hjl, Set.inter_self]
    · rw [ite_eq_left List.mem_cons_self, ite_eq_right hjl, Set.inter_eq_left.mpr (hXsub j)]
  · rw [updTuple_apply_ne (X a) hja]
    by_cases hjl : j ∈ l
    · rw [ite_eq_left (List.mem_cons_of_mem a hjl), ite_eq_left hjl, Set.inter_eq_right.mpr (hXsub j)]
    · rw [ite_eq_right fun h => (List.mem_cons.mp h).elim hja hjl, ite_eq_right hjl, Set.inter_self]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
/-- A cylinder is contained in each of its own slices. -/
theorem iprodNbhd_subset_slice {X : ∀ i, Set (α i)} (hX : ∀ i, (D i).mem (X i)) (i : ι) :
    iprodNbhd X ⊆ slice D i (X i) := by
  rw [slice_eq, iprodNbhd_subset_iff]
  intro j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self]
  · rw [updTuple_apply_ne (X i) h]; exact (D j).sub_master (hX j)

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- A slice has support `⊆ {i}`, hence is a neighbourhood of the product when `U ∈ 𝒟ᵢ`. -/
theorem iprod_mem_slice {i : ι} {U : Set (α i)} (hU : (D i).mem U) :
    (iprod D).mem (slice D i U) := by
  refine ⟨updTuple D i U, fun j => ?_, ⟨[i], fun j hj => ?_⟩, rfl⟩
  · by_cases h : j = i
    · subst h; rw [updTuple_apply_self]; exact hU
    · rw [updTuple_apply_ne U h]; exact (D j).master_mem
  · exact updTuple_apply_ne U fun h => hj (List.mem_singleton.mpr h)

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
/-- Slices at the same coordinate intersect by intersecting their data. -/
theorem slice_inter (i : ι) (U U' : Set (α i)) :
    slice D i U ∩ slice D i U' = slice D i (U ∩ U') := by
  rw [slice_eq, slice_eq, slice_eq, iprodNbhd_inter]
  congr 1; funext j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self, updTuple_apply_self, updTuple_apply_self]
  · rw [updTuple_apply_ne U h, updTuple_apply_ne U' h, updTuple_apply_ne (U ∩ U') h,
      Set.inter_self]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
/-- Slices are monotone in their data. -/
theorem slice_subset (i : ι) {U U' : Set (α i)} (hUU' : U ⊆ U') : slice D i U ⊆ slice D i U' := by
  rw [slice_eq, slice_eq, iprodNbhd_subset_iff]
  intro j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self, updTuple_apply_self]; exact hUU'
  · rw [updTuple_apply_ne U h, updTuple_apply_ne U' h]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- **The `i`-th component of a product element** (Scott's `z_i`). -/
def proj (z : (iprod D).Element) (i : ι) : (D i).Element where
  mem U := (D i).mem U ∧ z.mem (slice D i U)
  sub h := h.1
  master_mem := ⟨(D i).master_mem, by
    have : slice D i (D i).master = (iprod D).master := by
      show iprodNbhd (updTuple D i (D i).master) = iprodNbhd (fun j => (D j).master)
      congr 1; funext j
      by_cases h : j = i
      · subst h; rw [updTuple_apply_self]
      · rw [updTuple_apply_ne (D i).master h]
    rw [this]; exact z.master_mem⟩
  inter_mem := by
    rintro U U' ⟨_, hzU⟩ ⟨_, hzU'⟩
    have hz := z.inter_mem hzU hzU'
    rw [slice_inter] at hz
    exact ⟨iprod_mem_slice_inv (z.sub hz), hz⟩
  up_mem := by
    rintro U U' ⟨_, hzU⟩ hU' hUU'
    exact ⟨hU', z.up_mem hzU (iprod_mem_slice hU') (slice_subset i hUU')⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

theorem proj_fromPi (x : ∀ i, (D i).Element) (i : ι) : proj (fromPi D x) i = x i := by
  apply Element.ext
  intro U
  constructor
  · rintro ⟨_, hz⟩; exact (fromPi_mem_slice x i U).mp hz
  · intro hU; exact ⟨(x i).sub hU, (fromPi_mem_slice x i U).mpr hU⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- An element contains the restricted cylinder once it contains each listed slice. -/
theorem z_mem_iprodNbhd_restrictTo (z : (iprod D).Element) {X : ∀ i, Set (α i)}
    (hXsub : ∀ i, X i ⊆ (D i).master) (hslice : ∀ i, z.mem (slice D i (X i))) (l : List ι) :
    z.mem (iprodNbhd (restrictTo D l X)) := by
  induction l with
  | nil =>
    have : restrictTo D [] X = fun j => (D j).master := by
      funext j; rw [restrictTo]; exact ite_eq_right List.not_mem_nil
    rw [this]; exact z.master_mem
  | cons a l ih =>
    rw [iprodNbhd_restrictTo_cons hXsub a l]
    exact z.inter_mem (hslice a) ih

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- **Reconstruction.** A product element containing each of a cylinder's slices contains the
cylinder. The finite support (a *list* of coordinates) lets the only finitely many non-trivial slices
be intersected inside the element — entirely choice-free. -/
theorem z_mem_of_slices (z : (iprod D).Element) {X : ∀ i, Set (α i)}
    (hXmem : ∀ i, (D i).mem (X i)) (hXf : FinSupp D X)
    (hslice : ∀ i, z.mem (slice D i (X i))) : z.mem (iprodNbhd X) := by
  obtain ⟨l, hl⟩ := hXf
  have hsub : ∀ i, X i ⊆ (D i).master := fun i => (D i).sub_master (hXmem i)
  have key := z_mem_iprodNbhd_restrictTo z hsub hslice l
  have heq : restrictTo D l X = X := by
    funext j
    rw [restrictTo]
    by_cases h : j ∈ l
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; exact (hl j h).symm
  rwa [heq] at key

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

theorem fromPi_toPi (z : (iprod D).Element) : fromPi D (fun i => proj z i) = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, hX, hXf, rfl⟩
    exact z_mem_of_slices z (fun i => (hX i).1) hXf (fun i => (hX i).2)
  · intro hW
    obtain ⟨X, hXmem, hXf, rfl⟩ := z.sub hW
    exact ⟨X, fun i => ⟨hXmem i, z.up_mem hW (iprod_mem_slice (hXmem i))
      (iprodNbhd_subset_slice hXmem i)⟩, hXf, rfl⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- **Exercise 6.29 — `×` generalizes to `∏`, correct up to isomorphism.** The domain of the
indexed product is the pointwise product of the factor domains: `|∏_i D_i| ≃o ∀ i, |D_i|`. This is
the infinitary **Proposition 3.2** (`prodEquiv`). -/
def iprodEquiv (D : ∀ i, NeighborhoodSystem (α i)) :
    (iprod D).Element ≃o (∀ i, (D i).Element) where
  toFun z := fun i => proj z i
  invFun x := fromPi D x
  left_inv z := fromPi_toPi z
  right_inv x := funext fun i => proj_fromPi x i
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hzW
      obtain ⟨X, hXmem, hXf, rfl⟩ := z.sub hzW
      refine z_mem_of_slices z' hXmem hXf fun i => ?_
      have hzi : (proj z i).mem (X i) :=
        ⟨hXmem i, z.up_mem hzW (iprod_mem_slice (hXmem i)) (iprodNbhd_subset_slice hXmem i)⟩
      exact ((h i) (X i) hzi).2
    · intro h i U hU
      exact ⟨hU.1, h _ hU.2⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


theorem injI_inter_ne {i j : ι} (h : i ≠ j) (X : Set (α i)) (Y : Set (α j)) :
    injI i X ∩ injI j Y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro (_ | ⟨k, a⟩) ⟨hw1, hw2⟩
  · exact none_not_mem_injI hw1
  · exact h ((index_of_some_mem_injI hw1).symm.trans (index_of_some_mem_injI hw2))

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


theorem injI_nonempty {i : ι} {X : Set (α i)} (hX : X.Nonempty) : (injI i X).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨some ⟨i, a⟩, some_mem_injI.mpr ha⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — `⊗` does not generalize.** Over an infinite index, the smash product has only
its basepoint: an all-coordinates-proper cylinder has support `Set.univ`, which cannot be finite. -/
theorem iotimes_only_master [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) :
    ∀ W, (iotimes D).mem W → W = (iotimes D).master := by
  rintro W (rfl | ⟨X, _, hXne, ⟨l, hl⟩, rfl⟩)
  · rfl
  · -- Every coordinate is proper, so the finite support list `l` would have to contain *all* of `ι`,
    -- impossible for an infinite index. This is a cardinality argument: Prop-level and unavoidably
    -- classical (Mathlib's `Set.Finite`/`Fintype` API is built on `Classical.choice`).
    refine absurd ((List.finite_toSet l).subset (fun i _ => ?_)) Set.infinite_univ
    exact not_not.mp fun hni => hXne i (hl i hni)

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — the infinite smash collapses to one point.** Its element domain is a
singleton (`⊥` only), so `⊗` has no sensible infinitary generalization. -/
theorem iotimes_subsingleton [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) :
    Subsingleton (iotimes D).Element := by
  refine ⟨fun x y => ?_⟩
  apply Element.ext
  intro W
  constructor
  · intro hx; rw [iotimes_only_master D W (x.sub hx)]; exact y.master_mem
  · intro hy; rw [iotimes_only_master D W (y.sub hy)]; exact x.master_mem

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


section IndexedProduct

variable [Nonempty ι]


theorem iprod_mem_iprodNbhd {X : ∀ i, Set (α i)} (hX : ∀ i, (D i).mem (X i))
    (hXf : FinSupp D X) : (iprod D).mem (iprodNbhd X) :=
  ⟨X, hX, hXf, rfl⟩

end IndexedProduct
end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — a sum element reaches at most one summand.** -/
theorem isum_summand_unique {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) {i j : ι} {X : Set (α i)} {Y : Set (α j)}
    (hX : z.mem (injI i X)) (hY : z.mem (injI j Y)) : i = j := by
  -- The filter element `z` contains the consistent intersection; its representative carries a
  -- token whose index is forced to be both `i` and `j` — no excluded middle on `i = j`.
  have hz := z.inter_mem hX hY
  rcases z.sub hz with h0 | ⟨k, W, hWmem, hWeq⟩
  · rw [Set.ext_iff] at h0
    exact absurd ((h0 none).mpr none_mem_sumMasterI).1 none_not_mem_injI
  · obtain ⟨w, hw⟩ := hne k W hWmem
    rw [Set.ext_iff] at hWeq
    have hmem := (hWeq (some ⟨k, w⟩)).mpr (some_mem_injI.mpr hw)
    obtain rfl := index_of_some_mem_injI hmem.1
    obtain rfl := index_of_some_mem_injI hmem.2
    rfl

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — sum trichotomy.** Every element of `∑_i D_i` either reaches into some summand
or is the basepoint `⊥`. (Prop-level and genuinely classical: the case split is excluded middle on
whether `z` reaches a summand, so this depends on `Classical.choice`.) -/
theorem isum_trichotomy {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) :
    (∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)) ∨
      (∀ W, z.mem W → W = (isum D hne).master) := by
  by_cases h : ∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)
  · exact Or.inl h
  · refine Or.inr fun W hW => ?_
    rcases z.sub hW with rfl | ⟨i, X, hX, rfl⟩
    · rfl
    · exact absurd ⟨i, X, hX, hW⟩ h

end Exercise629
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise629
section
set_option linter.unusedVariables false

theorem example_629.{u, v} : And
  (And
    (And
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D))))
    (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
      {hne :
        ∀ (i : ι) (X : Set (α i)),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))
      {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
          (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X) →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α j Y) →
          @Eq ι i j))
  (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
    {hne :
      ∀ (i : ι) (X : Set (α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
    (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
        (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne)),
    Or
      (∃ (i : ι) (X : Set (α i)),
        And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X)))
      (∀ (W : Set (Option (@Sigma ι fun (i : ι) => α i))),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z W →
          @Eq (Set (Option (@Sigma ι fun (i : ι) => α i))) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (Option (@Sigma ι fun (i : ι) => α i))
              (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne)))) :=
  @And.intro
  (And
    (And
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D))))
    (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
      {hne :
        ∀ (i : ι) (X : Set (α i)),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))
      {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
          (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X) →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α j Y) →
          @Eq ι i j))
  (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
    {hne :
      ∀ (i : ι) (X : Set (α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
    (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
        (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne)),
    Or
      (∃ (i : ι) (X : Set (α i)),
        And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X)))
      (∀ (W : Set (Option (@Sigma ι fun (i : ι) => α i))),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z W →
          @Eq (Set (Option (@Sigma ι fun (i : ι) => α i))) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (Option (@Sigma ι fun (i : ι) => α i))
              (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))))
  (@And.intro
    (And
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D))))
    (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
      {hne :
        ∀ (i : ι) (X : Set (α i)),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))
      {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
          (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X) →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α j Y) →
          @Eq ι i j)
    (@And.intro
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      @DomainTheory.NeighbourhoodSystems.Exercise629.iotimes_only_master
      @DomainTheory.NeighbourhoodSystems.Exercise629.iotimes_subsingleton)
    @DomainTheory.NeighbourhoodSystems.Exercise629.isum_summand_unique)
  @DomainTheory.NeighbourhoodSystems.Exercise629.isum_trichotomy
end

end DomainTheory.NeighbourhoodSystems.Exercise629
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Scott's `⊴` (the prose before Lemma 6.15).** `D ⊴ E` means `D ≅ D'` for some subdomain
`D' ◁ E`: `D` *embeds as a subdomain* of `E`. -/
def Trianglelefteq (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) : Prop :=
  ∃ D' : NeighborhoodSystem β, D' ◁ E ∧ (D ≅ᴰ D')
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

@[inherit_doc] infix:50 " ⊴ " => Trianglelefteq
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- The generator predicate: `Y` generates `i(↑X)`. Relationally, `X i Y` and `Y j X`. -/
def IsGen (X : Set α) (Y : Set β) : Prop := i.rel X Y ∧ j.rel Y X

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **Generators exist** (uses `j ∘ i = I_D`). Every `D`-neighbourhood `X` has a generator: apply
`j ∘ i = I_D` to the identity relation `X I_D X`. -/
theorem isGen_exists (hji : j.comp i = idMap D) {X : Set α} (hX : D.mem X) :
    ∃ Y, IsGen i j X Y := by
  have hrel : (j.comp i).rel X X := by rw [hji]; exact ⟨hX, hX, subset_rfl⟩
  obtain ⟨Y, hiXY, hjYX⟩ := hrel
  exact ⟨Y, hiXY, hjYX⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **Generators are closed under intersection.** If `Y, Y'` generate `X, X'` and `Y ∩ Y' ∈ E`, then
`Y ∩ Y'` generates `X ∩ X'`. Needs only `mono`/`inter_right` of `i` and `j` (the hypothesis
`E.mem (Y ∩ Y')` is what licenses the `j.mono` steps). -/
theorem isGen_inter {X X' : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y') (hE : E.mem (Y ∩ Y')) :
    IsGen i j (X ∩ X') (Y ∩ Y') := by
  obtain ⟨hiXY, hjYX⟩ := h
  obtain ⟨hiX'Y', hjY'X'⟩ := h'
  have hj1 : j.rel (Y ∩ Y') X :=
    j.mono hjYX Set.inter_subset_left subset_rfl hE (j.rel_cod hjYX)
  have hj2 : j.rel (Y ∩ Y') X' :=
    j.mono hjY'X' Set.inter_subset_right subset_rfl hE (j.rel_cod hjY'X')
  have hjInter : j.rel (Y ∩ Y') (X ∩ X') := j.inter_right hj1 hj2
  have hDXX' : D.mem (X ∩ X') := j.rel_cod hjInter
  have hi1 : i.rel (X ∩ X') Y :=
    i.mono hiXY Set.inter_subset_left subset_rfl hDXX' (i.rel_cod hiXY)
  have hi2 : i.rel (X ∩ X') Y' :=
    i.mono hiX'Y' Set.inter_subset_right subset_rfl hDXX' (i.rel_cod hiX'Y')
  exact ⟨i.inter_right hi1 hi2, hjInter⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- The masters generate each other: `IsGen Δ_D Δ_E` (from `i.master_rel`, `j.master_rel`). -/
theorem isGen_master : IsGen i j D.master E.master :=
  ⟨i.master_rel, j.master_rel⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The image subdomain `D'`.** A `β`-set `Y` is a neighbourhood iff it generates some
`D`-neighbourhood; the master is `E`'s master. `isGen_inter` supplies condition (ii). -/
def Dprime : NeighborhoodSystem β where
  mem Y := ∃ X, IsGen i j X Y
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨D.master, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ Z ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ ⟨_, hgz⟩ hZsub
    have hEY₁ : E.mem Y₁ := i.rel_cod hg₁.1
    have hEY₂ : E.mem Y₂ := i.rel_cod hg₂.1
    have hEZ : E.mem Z := i.rel_cod hgz.1
    have hEinter : E.mem (Y₁ ∩ Y₂) := E.inter_mem hEY₁ hEY₂ hEZ hZsub
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hEinter⟩
  sub_master := by
    rintro Y ⟨X, hg⟩
    exact E.sub_master (i.rel_cod hg.1)

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The generator correspondence is monotone** (uses `j ∘ i = I_D`): if `Y, Y'` generate `X, X'`
and `Y ⊆ Y'`, then `X ⊆ X'`. (Widen `X i Y` to `X i Y'` by `mono`, compose with `Y' j X'`, and read
off `X ⊆ X'` from `j ∘ i = I_D`.) -/
theorem isGen_mono (hji : j.comp i = idMap D) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hZW : Z ⊆ W) : X ⊆ X' := by
  obtain ⟨hiXZ, _⟩ := h
  obtain ⟨_, hjWX'⟩ := h'
  have hiXW : i.rel X W :=
    i.mono hiXZ subset_rfl hZW (i.rel_dom hiXZ) (j.rel_dom hjWX')
  have hrel : (j.comp i).rel X X' := ⟨W, hiXW, hjWX'⟩
  rw [hji] at hrel
  exact hrel.2.2

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- Generators are unique in the first argument (`isGen_mono` both ways). -/
theorem isGen_fst_unique (hji : j.comp i = idMap D) {X X' : Set α} {Y : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y) : X = X' :=
  Set.Subset.antisymm (isGen_mono i j hji h h' subset_rfl)
    (isGen_mono i j hji h' h subset_rfl)

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The generator correspondence is monotone, other direction** (uses `i ∘ j ⊆ I_E`): if `Z, W`
generate `X, X'` and `X ⊆ X'`, then `Z ⊆ W`. (Widen `Z j X` to `Z j X'` by `mono`, compose with
`X' i W`, and read off `Z ⊆ W` from `i ∘ j ⊆ I_E`.) -/
theorem isGen_mono' (hij : i.comp j ≤ idMap E) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hXX' : X ⊆ X') : Z ⊆ W := by
  obtain ⟨_, hjZX⟩ := h
  obtain ⟨hiX'W, _⟩ := h'
  have hjZX' : j.rel Z X' :=
    j.mono hjZX subset_rfl hXX' (j.rel_dom hjZX) (i.rel_dom hiX'W)
  have hrel : (i.comp j).rel Z W := ⟨X', hjZX', hiX'W⟩
  exact (hij Z W hrel).2.2

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- Generators are unique in the second argument (`isGen_mono'` both ways). -/
theorem isGen_snd_unique (hij : i.comp j ≤ idMap E) {X : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X Y') : Y = Y' :=
  Set.Subset.antisymm (isGen_mono' i j hij h h' subset_rfl)
    (isGen_mono' i j hij h' h subset_rfl)

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

@[simp] theorem mem_Dprime {Y : Set β} : (Dprime i j).mem Y ↔ ∃ X, IsGen i j X Y := Iff.rfl

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **`D' ◁ E`.** Same master (`rfl`); `D' ⊆ E` since a generator's `Y` is an `E`-neighbourhood; and
the consistency clause `inter_closed` is exactly `isGen_inter`. -/
theorem Dprime_subsystem : Dprime i j ◁ E where
  master_eq := rfl
  sub := by rintro Y ⟨X, hg⟩; exact i.rel_cod hg.1
  inter_closed := by
    rintro Y₁ Y₂ ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ hE
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hE⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **Inverse map of the isomorphism `D ≅ D'`.** `y ↦ {X ∣ ∃ Y ∈ y, IsGen i j X Y}`. (Needs both
laws: `j ∘ i = I_D` for generator existence and `i ∘ j ⊆ I_E` for `isGen_mono'`.) -/
def ofEl (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E)
    (y : (Dprime i j).Element) : D.Element where
  mem X := ∃ Y, y.mem Y ∧ IsGen i j X Y
  sub := by rintro X ⟨Y, _, hg⟩; exact i.rel_dom hg.1
  master_mem := ⟨E.master, y.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro X₁ X₂ ⟨Y₁, hY₁y, hg₁⟩ ⟨Y₂, hY₂y, hg₂⟩
    have hyInter : y.mem (Y₁ ∩ Y₂) := y.inter_mem hY₁y hY₂y
    have hEInter : E.mem (Y₁ ∩ Y₂) := (Dprime_subsystem i j).sub (y.sub hyInter)
    exact ⟨Y₁ ∩ Y₂, hyInter, isGen_inter i j hg₁ hg₂ hEInter⟩
  up_mem := by
    rintro X X' ⟨Y, hYy, hg⟩ hDX' hXX'
    obtain ⟨Y', hg'⟩ := isGen_exists i j hji hDX'
    have hYY' : Y ⊆ Y' := isGen_mono' i j hij hg hg' hXX'
    exact ⟨Y', y.up_mem hYy ⟨X', hg'⟩ hYY', hg'⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **Forward map of the isomorphism `D ≅ D'`.** `x ↦ {Y ∣ ∃ X ∈ x, IsGen i j X Y}` — the
generators of the members of `x`. (Needs `j ∘ i = I_D` for upward closure, via `isGen_mono`.) -/
def toEl (hji : j.comp i = idMap D) (x : D.Element) : (Dprime i j).Element where
  mem Y := ∃ X, x.mem X ∧ IsGen i j X Y
  sub := by rintro Y ⟨X, _, hg⟩; exact ⟨X, hg⟩
  master_mem := ⟨D.master, x.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ ⟨X₁, hX₁x, hg₁⟩ ⟨X₂, hX₂x, hg₂⟩
    have hxInter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁x hX₂x
    have hDInter : D.mem (X₁ ∩ X₂) := x.sub hxInter
    have hi1 : i.rel (X₁ ∩ X₂) Y₁ :=
      i.mono hg₁.1 Set.inter_subset_left subset_rfl hDInter (i.rel_cod hg₁.1)
    have hi2 : i.rel (X₁ ∩ X₂) Y₂ :=
      i.mono hg₂.1 Set.inter_subset_right subset_rfl hDInter (i.rel_cod hg₂.1)
    have hEinter : E.mem (Y₁ ∩ Y₂) := i.rel_cod (i.inter_right hi1 hi2)
    exact ⟨X₁ ∩ X₂, hxInter, isGen_inter i j hg₁ hg₂ hEinter⟩
  up_mem := by
    rintro Y Y' ⟨X, hXx, hg⟩ ⟨X', hg'⟩ hYY'
    have hXX' : X ⊆ X' := isGen_mono i j hji hg hg' hYY'
    exact ⟨X', x.up_mem hXx (i.rel_dom hg'.1) hXX', hg'⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The domain isomorphism `D ≅ D'`** (Scott's "inclusion-preserving one-one correspondence").
Built from `toEl`/`ofEl`; the inverse laws and order-reflection come from generator uniqueness. -/
def dprimeEquiv (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E) :
    D.Element ≃o (Dprime i j).Element where
  toFun := toEl i j hji
  invFun := ofEl i j hji hij
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨Y, ⟨X₁, hX₁x, hg₁⟩, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x
    · intro hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      exact ⟨Y, ⟨X, hXx, hg⟩, hg⟩
  right_inv := by
    intro y
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨X, ⟨Y₁, hY₁y, hg₁⟩, hg⟩
      rw [isGen_snd_unique i j hij hg hg₁]; exact hY₁y
    · intro hYy
      obtain ⟨X, hg⟩ := y.sub hYy
      exact ⟨X, ⟨Y, hYy, hg⟩, hg⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      obtain ⟨X₁, hX₁x', hg₁⟩ := h Y ⟨X, hXx, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x'
    · rintro h Y ⟨X, hXx, hg⟩
      exact ⟨X, h X hXx, hg⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

end
end DomainTheory.NeighbourhoodSystems
end
