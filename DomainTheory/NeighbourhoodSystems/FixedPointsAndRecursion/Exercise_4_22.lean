module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_24
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_2_3
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Definition_4_5
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_14

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise422
open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- Scott's operator `g(x) = {0} ∪ x⁺` on `P(N*)`, whose least fixed point is the smallest subset
containing `0` and closed under the successor. -/
def genOp (x : Set M) : Set M := {zero} ∪ succ '' x
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- *(For set theorists.)* The standard natural numbers `⟨ℕ, 0, ⁺⟩` form a model of Peano's Axioms;
their existence is the **axiom of infinity**. (This witnesses that an `N*` satisfying (i)/(ii) — in
fact all three — exists in the first place.) -/
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
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- The carved-out subset `N ⊆ N*`: the least fixed point of `g` (Exercise 4.13(2)/4.14). -/
def nats : Set M := lfpSet (genOp zero succ)
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- The subtype `N = {m // m ∈ nats}` carrying the carved-out Peano structure. -/
abbrev Nat' : Type _ := {m : M // m ∈ nats zero succ}
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- **Induction by minimality.** Any subset `s ⊆ N*` containing `0` and closed under `⁺` contains
all of `N`. (This is the heart of axiom (iii): `s` is a pre-fixed point of `g`, hence dominates the
least fixed point `nats`.) -/
theorem nats_induction (s : Set M) (h0 : zero ∈ s) (hsucc : ∀ n ∈ s, succ n ∈ s) :
    nats zero succ ⊆ s := by
  apply lfpSet_subset (genOp zero succ)
  rintro x (rfl | ⟨n, hn, rfl⟩)
  · exact h0
  · exact hsucc n hn
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- `N` is closed under the successor: `n ∈ N ⟹ n⁺ ∈ N` — again directly from `lfpSet`. -/
theorem succ_mem_nats {n : M} (hn : n ∈ nats zero succ) : succ n ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inr ⟨n, hn x hx, rfl⟩)
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- The successor of the subtype (well-defined by closure `succ_mem_nats`). -/
def subSucc (n : Nat' zero succ) : Nat' zero succ := ⟨succ n.1, succ_mem_nats zero succ n.2⟩
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- `0 ∈ N` — directly from the `lfpSet` definition (no monotonicity needed), keeping the
construction choice-free. -/
theorem zero_mem_nats : zero ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inl rfl)
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- The zero of the subtype. -/
def subZero : Nat' zero succ := ⟨zero, zero_mem_nats zero succ⟩
end

section
variable {M : Type*} (zero : M) (succ : M → M)

end
end DomainTheory.NeighbourhoodSystems.Exercise422

section
namespace DomainTheory.NeighbourhoodSystems.Exercise422
open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414
section
variable {M : Type*} (zero : M) (succ : M → M)
/- concordance: source L2347 EXERCISE 4.22 inductive subset of a model -/
/-- **Exercise 4.22 (Scott 1981, PRG-19).** The carved-out subset `N ⊆ N*`, with the inherited
`0` and `⁺`, is a model of **all three** Peano axioms — even though `N*` was only assumed to satisfy
(i) and (ii). Axioms (i)/(ii) are inherited; (iii) holds by minimality of the least fixed point. -/
def peanoSub (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    PeanoModel (Nat' zero succ) where
  zero := subZero zero succ
  succ := subSucc zero succ
  zero_ne_succ n h := hzero n.1 (Subtype.ext_iff.mp h)
  succ_injective a b h := Subtype.ext (hinj (Subtype.ext_iff.mp h))
  induction s h0 hstep := by
    -- pull `s` back to a subset of `N*`, show it is closed under `0`/`⁺`, apply `nats_induction`
    intro n
    have hsub : nats zero succ ⊆
        {m | ∃ h : m ∈ nats zero succ, (⟨m, h⟩ : Nat' zero succ) ∈ s} := by
      apply nats_induction zero succ
      · exact ⟨zero_mem_nats zero succ, h0⟩
      · rintro m ⟨hmnat, hms⟩
        exact ⟨succ_mem_nats zero succ hmnat, hstep ⟨m, hmnat⟩ hms⟩
    obtain ⟨_, hns⟩ := hsub n.2
    exact hns
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- **Exercise 4.22 (Scott 1981, PRG-19).** *Yes:* whenever `N*` satisfies (i) and (ii), there is a
subset `N ⊆ N*` (carrying the inherited structure) satisfying (i), (ii), and (iii). -/
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
end

section
variable {M : Type*} (zero : M) (succ : M → M)

theorem genOp_nats : genOp zero succ (nats zero succ) = nats zero succ :=
  lfpSet_isFixed (genOp zero succ) (genOp_monotone zero succ)
end

end DomainTheory.NeighbourhoodSystems.Exercise422
end
