module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem_1_11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise113
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

theorem branch_isTotal (p : ℕ → Bool) : B.IsTotal (branch p) := by
  intro y hy X hX
  obtain ⟨σ, rfl⟩ := y.sub hX
  have hk : y.mem (cone (prefixSeq p σ.length)) :=
    hy _ ((branch_mem_iff p).mpr ⟨σ.length, List.prefix_rfl⟩)
  rcases prefix_comparable_of_mem y hX hk with h | h
  · exact (branch_mem_iff p).mpr ⟨σ.length, h⟩
  · have hlen : (prefixSeq p σ.length).length = σ.length := prefixSeq_length p σ.length
    have hσ : prefixSeq p σ.length = σ := h.eq_of_length hlen
    exact (branch_mem_iff p).mpr ⟨σ.length, by rw [hσ]⟩

section
set_option linter.unusedVariables false

theorem example_113 : ∀ (p : Nat → Bool),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal DomainTheory.NeighbourhoodSystems.ExampleB.Str
    DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise113.branch p) :=
  DomainTheory.NeighbourhoodSystems.Exercise113.branch_isTotal
end
end

end DomainTheory.NeighbourhoodSystems.Exercise113
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

theorem le_iInter (x : ℕ → V.Element) (y : V.Element) (h : ∀ n, y ≤ x n) :
    y ≤ V.iInter x :=
  fun X hX n => h n X hX

theorem le_iUnion (x : ℕ → V.Element) (hmono : Monotone x) (n : ℕ) :
    x n ≤ V.iUnion x hmono :=
  fun _ hX => ⟨n, hX⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise113
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

theorem branchSeq_le_branch (p : ℕ → Bool) (n : ℕ) : branchSeq p n ≤ branch p :=
  B.le_iUnion (branchSeq p) (branchSeq_mono p) n
end

end DomainTheory.NeighbourhoodSystems.Exercise113
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

theorem interUpTo_antitone (X : ℕ → Set α) {j k : ℕ} (h : j ≤ k) :
    V.interUpTo X k ⊆ V.interUpTo X j := by
  induction k with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact Set.inter_subset_left.trans (ih (Nat.lt_succ_iff.mp h'))
end

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end
