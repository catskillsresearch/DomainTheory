module

import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_5
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_1
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_19

@[expose] public section

section
-- Exercise118/FinitelyConsistent.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L466 EXERCISE 1.18 consistency of neighbourhood families -/
/-- **Exercise 1.18 — consistent subset.** `C ⊆ 𝒟` is *finitely consistent* iff every finite
sequence drawn from `C` is `Consistent` in `𝒟`. -/
def FinitelyConsistent (C : Set (Set α)) : Prop :=
  ∀ (n : ℕ) (X : ℕ → Set α), (∀ i, i < n → X i ∈ C) → V.Consistent X n

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/appendSeq.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

/-- Concatenation of two finite sequences: the first `n1` entries are `X1 0, …, X1 (n1-1)`,
then `X2 0, X2 1, …`. -/
def appendSeq {α : Type*} (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) : ℕ → Set α :=
  fun i => if i < n1 then X1 i else X2 (i - n1)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/appendSeq_mem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

/-- Each entry of `appendSeq X1 n1 X2` below `n1 + n2` is drawn from `C`. -/
theorem appendSeq_mem {α : Type*} {C : Set (Set α)} {X1 : ℕ → Set α} {n1 : ℕ}
    {X2 : ℕ → Set α} {n2 : ℕ} (h1 : ∀ i, i < n1 → X1 i ∈ C) (h2 : ∀ i, i < n2 → X2 i ∈ C) :
    ∀ i, i < n1 + n2 → appendSeq X1 n1 X2 i ∈ C := by
  intro i hi
  simp only [appendSeq]
  by_cases h : i < n1
  · rw [ite_eq_left h]; exact h1 i h
  · rw [ite_eq_right h]; exact h2 (i - n1) (by omega)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/A.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `A = {0,1}`. -/
def A : Set (Fin 3) := {0, 1}

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/B.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `B = {1,2}`. -/
def B : Set (Fin 3) := {1, 2}

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/Cc.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `Cc = {0,2}`. -/
def Cc : Set (Fin 3) := {0, 2}

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/family.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- The three-member family `C = {A, B, Cc}`. -/
def family : Set (Set (Fin 3)) := {A, B, Cc}

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/interUpTo_appendSeq_left.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- For a prefix length `k ≤ n1`, `interUpTo` of the appended sequence agrees with `interUpTo`
of the first sequence. -/
theorem interUpTo_appendSeq_left (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) :
    ∀ {k : ℕ}, k ≤ n1 → V.interUpTo (appendSeq X1 n1 X2) k = V.interUpTo X1 k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [interUpTo_succ, interUpTo_succ, ih (Nat.le_of_succ_le hk)]
    have happ : appendSeq X1 n1 X2 k = X1 k := by
      simp only [appendSeq, ite_eq_left (Nat.lt_of_succ_le hk)]
    rw [happ]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/interUpTo_subset_master.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection is contained in the master neighbourhood (its first factor). -/
theorem interUpTo_subset_master (X : ℕ → Set α) : ∀ n, V.interUpTo X n ⊆ V.master := by
  intro n
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact Set.inter_subset_left.trans ih

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/interUpTo_appendSeq.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The key identity: `⋂_{i<n1+n2} (X1 ⧺ X2)ᵢ = (⋂_{i<n1} X1ᵢ) ∩ (⋂_{i<n2} X2ᵢ)`. -/
theorem interUpTo_appendSeq (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) :
    ∀ {j : ℕ}, V.interUpTo (appendSeq X1 n1 X2) (n1 + j)
      = V.interUpTo X1 n1 ∩ V.interUpTo X2 j := by
  intro j
  induction j with
  | zero =>
    rw [Nat.add_zero, V.interUpTo_appendSeq_left X1 n1 X2 (le_refl n1), interUpTo_zero]
    exact (Set.inter_eq_left.mpr (V.interUpTo_subset_master X1 n1)).symm
  | succ j ih =>
    rw [Nat.add_succ, interUpTo_succ, ih]
    have happ : appendSeq X1 n1 X2 (n1 + j) = X2 j := by
      simp only [appendSeq, ite_eq_right (by omega : ¬ n1 + j < n1)]
      congr 1
      omega
    rw [happ, interUpTo_succ, Set.inter_assoc]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/leastFilter.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.18 — the least filter containing a consistent `C`.**
`leastFilter C = {Y ∈ 𝒟 ∣ ⋂_{i<n} Xᵢ ⊆ Y for some finite sequence ⟨Xᵢ⟩ from C}`. The
intersection law concatenates two finite sequences (`interUpTo_appendSeq`) and uses finite
consistency to keep their combined intersection in `𝒟`. -/
def leastFilter (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) : V.Element where
  mem Y := V.mem Y ∧ ∃ (n : ℕ) (X : ℕ → Set α), (∀ i, i < n → X i ∈ C) ∧ V.interUpTo X n ⊆ Y
  sub h := h.1
  master_mem :=
    ⟨V.master_mem, 0, (fun _ => V.master), (fun i hi => absurd hi (Nat.not_lt_zero i)),
      V.interUpTo_subset_master _ 0⟩
  inter_mem := by
    rintro X Y ⟨hXmem, n1, X1, hX1C, hX1sub⟩ ⟨hYmem, n2, X2, hX2C, hX2sub⟩
    have hmemC : ∀ i, i < n1 + n2 → appendSeq X1 n1 X2 i ∈ C := appendSeq_mem hX1C hX2C
    have hintermem : V.mem (V.interUpTo (appendSeq X1 n1 X2) (n1 + n2)) :=
      (V.consistent_iff_interUpTo_mem _ (fun i hi => hCsub _ (hmemC i hi))).mp
        (hC _ _ hmemC)
    have hsub : V.interUpTo (appendSeq X1 n1 X2) (n1 + n2) ⊆ X ∩ Y := by
      rw [V.interUpTo_appendSeq X1 n1 X2]
      exact Set.inter_subset_inter hX1sub hX2sub
    exact ⟨V.inter_mem hXmem hYmem hintermem hsub, n1 + n2, appendSeq X1 n1 X2, hmemC, hsub⟩
  up_mem := by
    rintro X Y ⟨_, n, Xs, hXC, hsub⟩ hY hXY
    exact ⟨hY, n, Xs, hXC, hsub.trans hXY⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/sInf.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.18 — the intersection of a non-empty family of filters is a filter.**
`sInf F = {X ∣ ∀ x ∈ F, X ∈ x}`. -/
def sInf (F : Set V.Element) (hF : F.Nonempty) : V.Element where
  mem X := ∀ x ∈ F, x.mem X
  sub h := hF.elim (fun x hx => x.sub (h x hx))
  master_mem := fun x _ => x.master_mem
  inter_mem h1 h2 := fun x hx => x.inter_mem (h1 x hx) (h2 x hx)
  up_mem h hY hXY := fun x hx => x.up_mem (h x hx) hY hXY

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triSys.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

/-- All non-empty subsets of `Δ = {0,1,2}` (a positive neighbourhood system). -/
def triSys : NeighborhoodSystem (Fin 3) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (⟨0, Set.mem_univ 0⟩) (⟨0, Set.mem_univ 0⟩)
    (fun {_} _ => Set.subset_univ _) (fun _ _ _ _ => Iff.rfl)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triple.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- The triple `A, B, Cc` as a finite sequence. -/
def triple : ℕ → Set (Fin 3) := fun i => if i = 0 then A else if i = 1 then B else Cc

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/family_pairwise_nonempty.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


/-- Every pair of members of `family` has non-empty intersection, hence (in the all-non-empty
system `triSys`) every pair is consistent. -/
theorem family_pairwise_nonempty :
    ∀ X ∈ family, ∀ Y ∈ family, (X ∩ Y).Nonempty := by
  intro X hX Y hY
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨2, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨2, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩

end triSys
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/le_sInf.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `sInf F` is the **greatest** lower bound of `F`. -/
theorem le_sInf (F : Set V.Element) (hF : F.Nonempty) (y : V.Element) (h : ∀ x ∈ F, y ≤ x) :
    y ≤ V.sInf F hF :=
  fun _ hX x hx => h x hx _ hX

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/leastFilter_le.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.18 — `leastFilter` is least.** Any filter `z` with `C ⊆ z` contains
`leastFilter C`. -/
theorem leastFilter_le (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) (z : V.Element) (hz : ∀ W ∈ C, z.mem W) :
    V.leastFilter C hCsub hC ≤ z := by
  rintro Y ⟨hYmem, n, X, hXC, hsub⟩
  exact z.up_mem (z.mem_interUpTo X (fun i hi => hz (X i) (hXC i hi))) hYmem hsub

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/sInf_le.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `sInf F ⊑ x` for every `x ∈ F`. -/
theorem sInf_le (F : Set V.Element) (hF : F.Nonempty) {x : V.Element} (hx : x ∈ F) :
    V.sInf F hF ≤ x :=
  fun _ h => h x hx

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/subset_leastFilter.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `C ⊆ leastFilter C`: every member of `C` is in the least filter. -/
theorem subset_leastFilter (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) {W : Set α} (hW : W ∈ C) :
    (V.leastFilter C hCsub hC).mem W := by
  refine ⟨hCsub W hW, 1, (fun _ => W), (fun _ _ => hW), ?_⟩
  rw [interUpTo_succ, interUpTo_zero]
  exact Set.inter_subset_right

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triSys_master.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


theorem triSys_master : triSys.master = (Set.univ : Set (Fin 3)) := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triple_interUpTo_empty.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


theorem triple_interUpTo_empty : triSys.interUpTo triple 3 = (∅ : Set (Fin 3)) := by
  simp only [NeighborhoodSystem.interUpTo_succ, NeighborhoodSystem.interUpTo_zero, triSys_master]
  ext x
  fin_cases x <;> simp [triple, A, B, Cc]

end triSys
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triple_mem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


theorem triple_mem : ∀ i, i < 3 → triple i ∈ family := by
  intro i hi
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end triSys
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/not_finitelyConsistent.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


/-- **Exercise 1.18 — `family` is pairwise consistent but not consistent.** Its full triple has
empty intersection, so no `Z ∈ 𝒟` (i.e. no non-empty `Z`) lies below it. -/
theorem not_finitelyConsistent : ¬ triSys.FinitelyConsistent family := by
  intro h
  obtain ⟨Z, hZmem, hZsub⟩ := h 3 triple triple_mem
  have hZne : Z.Nonempty := hZmem
  rw [triple_interUpTo_empty, Set.subset_empty_iff] at hZsub
  rw [hZsub] at hZne
  exact Set.not_nonempty_empty hZne

end triSys
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_118.{u_1} : And
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (C : Set (Set α))
    (hCsub :
      ∀ (X : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
    (hC : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent α V C)
    (z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    (∀ (W : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C W →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V z W) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.leastFilter α V C hCsub hC) z)
  (Not
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent
      (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) DomainTheory.NeighbourhoodSystems.triSys
      DomainTheory.NeighbourhoodSystems.triSys.family)) :=
  @And.intro
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (C : Set (Set α))
    (hCsub :
      ∀ (X : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
    (hC : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent α V C)
    (z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    (∀ (W : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C W →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V z W) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.leastFilter α V C hCsub hC) z)
  (Not
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent
      (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) DomainTheory.NeighbourhoodSystems.triSys
      DomainTheory.NeighbourhoodSystems.triSys.family))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.leastFilter_le)
  DomainTheory.NeighbourhoodSystems.triSys.not_finitelyConsistent

end DomainTheory.NeighbourhoodSystems
end
