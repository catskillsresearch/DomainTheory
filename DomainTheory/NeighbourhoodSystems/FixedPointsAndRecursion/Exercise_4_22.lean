module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Definition_4_5
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_14

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise422
open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

section
variable {M : Type*} (zero : M) (succ : M → M)

def genOp (x : Set M) : Set M := {zero} ∪ succ '' x

def natPeano : PeanoModel ℕ where
  zero := 0
  succ := Nat.succ
  zero_ne_succ n := (Nat.succ_ne_zero n).symm
  succ_injective := Nat.succ_injective
  induction s h0 hstep := by
    intro n
    induction n with
    | zero => exact h0
    | succ k ih => exact hstep k ih

def nats : Set M := lfpSet (genOp zero succ)

abbrev Nat' : Type _ := {m : M // m ∈ nats zero succ}

theorem nats_induction (s : Set M) (h0 : zero ∈ s) (hsucc : ∀ n ∈ s, succ n ∈ s) :
    nats zero succ ⊆ s := by
  apply lfpSet_subset (genOp zero succ)
  rintro x (rfl | ⟨n, hn, rfl⟩)
  · exact h0
  · exact hsucc n hn

theorem succ_mem_nats {n : M} (hn : n ∈ nats zero succ) : succ n ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inr ⟨n, hn x hx, rfl⟩)

def subSucc (n : Nat' zero succ) : Nat' zero succ := ⟨succ n.1, succ_mem_nats zero succ n.2⟩

theorem zero_mem_nats : zero ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inl rfl)

def subZero : Nat' zero succ := ⟨zero, zero_mem_nats zero succ⟩
end
end DomainTheory.NeighbourhoodSystems.Exercise422

section
namespace DomainTheory.NeighbourhoodSystems.Exercise422
open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414
section
variable {M : Type*} (zero : M) (succ : M → M)

def peanoSub (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    PeanoModel (Nat' zero succ) where
  zero := subZero zero succ
  succ := subSucc zero succ
  zero_ne_succ n h := hzero n.1 (Subtype.ext_iff.mp h)
  succ_injective a b h := Subtype.ext (hinj (Subtype.ext_iff.mp h))
  induction s h0 hstep := by

    intro n
    have hsub : nats zero succ ⊆
        {m | ∃ h : m ∈ nats zero succ, (⟨m, h⟩ : Nat' zero succ) ∈ s} := by
      apply nats_induction zero succ
      · exact ⟨zero_mem_nats zero succ, h0⟩
      · rintro m ⟨hmnat, hms⟩
        exact ⟨succ_mem_nats zero succ hmnat, hstep ⟨m, hmnat⟩ hms⟩
    obtain ⟨_, hns⟩ := hsub n.2
    exact hns

theorem exists_peano_submodel (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    Nonempty (PeanoModel (Nat' zero succ)) :=
  ⟨peanoSub zero succ hzero hinj⟩

end

section
set_option linter.unusedVariables false

theorem example_422.{u_1} : ∀ {M : Type u_1} (zero : M) (succ : M → M),
  (∀ (n : M), @Ne M zero (succ n)) →
    @Function.Injective M M succ →
      Nonempty
        (DomainTheory.NeighbourhoodSystems.PeanoModel (@DomainTheory.NeighbourhoodSystems.Exercise422.Nat' M zero succ)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise422.exists_peano_submodel
end

section
variable {M : Type*} (zero : M) (succ : M → M)

theorem genOp_monotone : Monotone (genOp zero succ) := by
  intro x y hxy z hz
  rcases hz with hz | ⟨a, ha, rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨a, hxy ha, rfl⟩

theorem genOp_nats : genOp zero succ (nats zero succ) = nats zero succ :=
  lfpSet_isFixed (genOp zero succ) (genOp_monotone zero succ)

end

end DomainTheory.NeighbourhoodSystems.Exercise422
end
