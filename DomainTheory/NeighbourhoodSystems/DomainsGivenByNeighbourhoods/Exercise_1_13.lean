module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.iUnion
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.IsTotal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.sigmaBot_le_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

def prefixSeq (p : ℕ → Bool) : ℕ → Str
  | 0 => []
  | (n + 1) => prefixSeq p n ++ [p n]

@[simp] theorem prefixSeq_length (p : ℕ → Bool) (n : ℕ) : (prefixSeq p n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [prefixSeq, ih]

def branchSeq (p : ℕ → Bool) (n : ℕ) : B.Element := sigmaBot (prefixSeq p n)

theorem prefixSeq_prefix_succ (p : ℕ → Bool) (n : ℕ) :
    prefixSeq p n <+: prefixSeq p (n + 1) := ⟨[p n], rfl⟩

theorem prefixSeq_mono (p : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    prefixSeq p n <+: prefixSeq p m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ k _ ih => exact ih.trans (prefixSeq_prefix_succ p k)

theorem branchSeq_mono (p : ℕ → Bool) : Monotone (branchSeq p) := by
  intro n m h
  exact (sigmaBot_le_iff (prefixSeq p n) (prefixSeq p m)).mpr (prefixSeq_mono p h)

def branch (p : ℕ → Bool) : B.Element := B.iUnion (branchSeq p) (branchSeq_mono p)

theorem branch_mem_iff (p : ℕ → Bool) {σ : Str} :
    (branch p).mem (cone σ) ↔ ∃ n, σ <+: prefixSeq p n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mp h
    exact ⟨n, cone.subset_cone.mp hn.2⟩
  · rintro ⟨n, hn⟩
    exact (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mpr
      ⟨n, memB_cone σ, cone.subset_cone.mpr hn⟩

theorem prefix_comparable_of_mem {σ τ : Str} (y : B.Element)
    (hσ : y.mem (cone σ)) (hτ : y.mem (cone τ)) : σ <+: τ ∨ τ <+: σ := by
  have hi : y.mem (cone σ ∩ cone τ) := y.inter_mem hσ hτ
  obtain ⟨ρ, hρ⟩ := y.sub hi
  rcases cone.trichotomy σ τ with h | h | h
  · exact Or.inr (cone.subset_cone.mp h)
  · exact Or.inl (cone.subset_cone.mp h)
  · exfalso
    have hmem : ρ ∈ cone ρ := cone.mem.mpr List.prefix_rfl
    rw [← hρ, h] at hmem
    simp at hmem

theorem branchSeq_le_branch (p : ℕ → Bool) (n : ℕ) : branchSeq p n ≤ branch p :=
  B.le_iUnion (branchSeq p) (branchSeq_mono p) n

theorem branch_isTotal (p : ℕ → Bool) : B.IsTotal (branch p) := by
  intro y hy X hX
  obtain ⟨σ, rfl⟩ := y.sub hX
  have hk : y.mem (cone (prefixSeq p σ.length)) :=
    hy _ ((branch_mem_iff p).mpr ⟨σ.length, List.prefix_rfl⟩)
  rcases prefix_comparable_of_mem y hX hk with h | h
  · exact (branch_mem_iff p).mpr ⟨σ.length, h⟩
  · have hlen : (prefixSeq p σ.length).length = σ.length := prefixSeq_length p σ.length
    have hσ : prefixSeq p σ.length = σ := h.eq_of_length hlen
    exact (branch_mem_iff p).mpr ⟨σ.length, by rw [hσ]; exact List.prefix_rfl⟩

theorem exercise_1_13 : ∀ p : ℕ → Bool, B.IsTotal (branch p) :=
  branch_isTotal

end DomainTheory.NeighbourhoodSystems.Exercise113
