module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_17

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

section
-- Exercise119/Tok.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- Tokens `Δ = {0, 1, 2}`. -/
abbrev Tok := Fin 3

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/a.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- The neighbourhood `{0, 1}`. -/
def a : Set Tok := {0, 1}

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/b.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- The neighbourhood `{1, 2}`. -/
def b : Set Tok := {1, 2}

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/master.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- The master neighbourhood `Δ`. -/
def master : Set Tok := Set.univ

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/memSet.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- `𝒟 = {Δ, {0,1}, {1,2}}`. -/
def memSet : Set (Set Tok) := {master, a, b}

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- Membership in `𝒟`. -/
def mem (X : Set Tok) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem_iff.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_iff (X : Set Tok) : mem X ↔ X = master ∨ X = a ∨ X = b := by
  simp only [mem, memSet, Set.mem_insert_iff, Set.mem_singleton_iff]

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/inter_eq.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- Classification of binary intersections in `𝒟`. -/
theorem inter_eq (X Y : Set Tok) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = a ∨ X ∩ Y = b ∨ X ∩ Y = ({1} : Set Tok) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inl (by ext x; fin_cases x <;> simp [master, a, b])
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b]))
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b])))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b]))
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b]))
    · exact Or.inr (Or.inr (Or.inr (by ext x; fin_cases x <;> simp [master, a, b])))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b])))
    · exact Or.inr (Or.inr (Or.inr (by ext x; fin_cases x <;> simp [master, a, b])))
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b])))

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem_a.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_a : mem a := (mem_iff _).mpr (Or.inr (Or.inl rfl))

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem_b.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_b : mem b := (mem_iff _).mpr (Or.inr (Or.inr rfl))

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem_master.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_master : mem master := (mem_iff _).mpr (Or.inl rfl)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/not_mem_sub_one.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- No neighbourhood is contained in `{1}` (each contains a token other than `1`). This is why
the overlapping pair `{0,1}`, `{1,2}` never triggers condition (ii). -/
theorem not_mem_sub_one {Z : Set Tok} (hZ : mem Z) (hsub : Z ⊆ ({1} : Set Tok)) : False := by
  rcases (mem_iff Z).mp hZ with rfl | rfl | rfl
  · exact absurd (hsub (show (0 : Tok) ∈ master by simp [master])) (by simp)
  · exact absurd (hsub (show (0 : Tok) ∈ a by simp [a])) (by simp)
  · exact absurd (hsub (show (2 : Tok) ∈ b by simp [b])) (by simp)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/notPositiveSystem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- **Exercise 1.19 — the non-positive example is a neighbourhood system.** The only intersection
that is not already a neighbourhood is `{0,1} ∩ {1,2} = {1}`, and that case is impossible: a
consistency witness `Z ⊆ {1}` with `Z ∈ 𝒟` does not exist (`not_mem_sub_one`). -/
def notPositiveSystem : NeighborhoodSystem Tok where
  mem := mem
  master := master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_a
    · rw [h]; exact mem_b
    · rw [h] at hZsub; exact (not_mem_sub_one hZ hZsub).elim

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/positiveExample.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- All non-empty subsets of `Fin 2` form a *positive* neighbourhood system: there `X ∩ Y ∈ 𝒟`
literally **is** `(X ∩ Y).Nonempty`, so (ii′) is `Iff.rfl`. -/
def positiveExample : NeighborhoodSystem (Fin 2) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (by exact ⟨(0 : Fin 2), Set.mem_univ 0⟩)
    (by exact ⟨(0 : Fin 2), Set.mem_univ 0⟩) (by intro X _; exact Set.subset_univ X)
    (by intro X Y _ _; exact Iff.rfl)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/a_inter_b.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems


/-- `{0,1} ∩ {1,2} = {1}`. -/
theorem a_inter_b : a ∩ b = ({1} : Set Tok) := by ext x; fin_cases x <;> simp [a, b]

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/one_not_mem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems


/-- `{1}` is not a neighbourhood (it is neither `Δ`, `{0,1}`, nor `{1,2}`). -/
theorem one_not_mem : ¬ mem ({1} : Set Tok) := by
  intro h
  rcases (mem_iff _).mp h with h | h | h
  · have h0 : (0 : Tok) ∈ master := by simp [master]
    rw [← h] at h0; simp at h0
  · have h0 : (0 : Tok) ∈ a := by simp [a]
    rw [← h] at h0; simp at h0
  · have h2 : (2 : Tok) ∈ b := by simp [b]
    rw [← h] at h2; simp at h2

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/not_isPositive.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems


/-- **Exercise 1.19 — the example is not positive.** `{0,1}` and `{1,2}` are neighbourhoods whose
intersection `{1}` is non-empty but is *not* a neighbourhood, contradicting (ii′). -/
theorem not_isPositive : ¬ notPositiveSystem.IsPositive := by
  intro h
  have hab := h (X := a) (Y := b) mem_a mem_b
  rw [a_inter_b] at hab
  exact one_not_mem (hab.mpr ⟨1, rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise119

set_option linter.unusedVariables false

theorem example_119 : Not
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive DomainTheory.NeighbourhoodSystems.Exercise119.Tok
    DomainTheory.NeighbourhoodSystems.Exercise119.notPositiveSystem) :=
  DomainTheory.NeighbourhoodSystems.Exercise119.not_isPositive

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/positiveExample_isPositive.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems


theorem positiveExample_isPositive : positiveExample.IsPositive := by
  intro X Y _ _
  exact Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Exercise 1.20's `↑X = {Y ∈ 𝒟 ∣ Y ⊆ X}` (the up-set of `X` *inside* `𝒟`). -/
def upSet (X : Set α) : Set (Set α) := {Y | V.mem Y ∧ Y ⊆ X}

@[simp] theorem mem_upSet {X Y : Set α} : Y ∈ V.upSet X ↔ V.mem Y ∧ Y ⊆ X := Iff.rfl

/-- `↑X ∩ ↑Y = ↑(X ∩ Y)` — a set identity (no membership hypotheses). -/
theorem upSet_inter (X Y : Set α) : V.upSet X ∩ V.upSet Y = V.upSet (X ∩ Y) := by
  ext Z
  simp only [Set.mem_inter_iff, mem_upSet, Set.subset_inter_iff]
  tauto

/-- `X ↦ ↑X` is inclusion-**preserving**: `↑X ⊆ ↑Y ↔ X ⊆ Y` (for `X ∈ 𝒟`).
`→` tests at `X ∈ ↑X`; `←` is transitivity of `⊆`. -/
theorem upSet_subset_iff {X Y : Set α} (hX : V.mem X) : V.upSet X ⊆ V.upSet Y ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h ⟨hX, subset_rfl⟩).2
  · intro hXY Z hZ
    exact ⟨hZ.1, hZ.2.trans hXY⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
