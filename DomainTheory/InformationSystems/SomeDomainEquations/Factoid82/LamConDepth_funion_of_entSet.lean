module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.funion_empty_right_lam
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_weaken_insert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_insert_le

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Prop 2.3(ii) via insert-first on `v`. -/
theorem LamConDepth_funion_of_entSet (M : ℕ)
    (ihIns : ∀ u t, Nat.max (finsetMaxDepth u) (rawDepth t) < M →
      LamEntDepth A u t → LamConDepth A (insert t u))
    {u v : Finset (RawLamToken α)}
    (hu : LamConDepth A u)
    (hEnt : ∀ t ∈ v, LamEntDepth A u t)
    (hbound : ∀ t ∈ v, Nat.max (finsetMaxDepth u) (rawDepth t) < M) :
    LamConDepth A (u ∪' v) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  suffices ∀ (v u : Finset (RawLamToken α)),
      LamConDepth A u →
      (∀ t ∈ v, LamEntDepth A u t) →
      (∀ t ∈ v, Nat.max (finsetMaxDepth u) (rawDepth t) < M) →
      LamConDepth A (u ∪' v) from
    this v u hu hEnt hbound
  intro v
  induction v using Finset.induction_on with
  | empty =>
    intro u hu _ _
    simpa [funion_empty_right_lam] using hu
  | insert a t ha ih =>
    intro u hu hEnt hbound
    have mem_a : a ∈ insert a t := Finset.mem_insert_self a t
    have han : Nat.max (finsetMaxDepth u) (rawDepth a) < M := hbound a mem_a
    have hEnt_a : LamEntDepth A u a := hEnt a mem_a
    have hu_ins : LamConDepth A (insert a u) := ihIns u a han hEnt_a
    have hEnt_t : ∀ x ∈ t, LamEntDepth A (insert a u) x := by
      intro x hx
      exact LamEntDepth_weaken_insert A hu_ins
        (hEnt x (Finset.mem_insert_of_mem hx)) hEnt_a
    have hbound_t : ∀ x ∈ t, Nat.max (finsetMaxDepth (insert a u)) (rawDepth x) < M := by
      intro x hx
      have hxu : Nat.max (finsetMaxDepth u) (rawDepth x) < M :=
        hbound x (Finset.mem_insert_of_mem hx)
      have hDi := finsetMaxDepth_insert_le u a
      have h1 : Nat.max (finsetMaxDepth (insert a u)) (rawDepth x) ≤
          Nat.max (Nat.max (rawDepth a) (finsetMaxDepth u)) (rawDepth x) :=
        max_le_max_nat hDi le_rfl
      refine Nat.lt_of_le_of_lt h1 ?_
      have h2 : Nat.max (Nat.max (rawDepth a) (finsetMaxDepth u)) (rawDepth x) =
          Nat.max (rawDepth a) (Nat.max (finsetMaxDepth u) (rawDepth x)) := by
        ac_rfl
      rw [h2]
      exact Nat.max_lt.2 ⟨Nat.lt_of_le_of_lt (Nat.le_max_right _ _) han, hxu⟩
    have hunion : LamConDepth A (insert a u ∪' t) :=
      ih (insert a u) hu_ins hEnt_t hbound_t
    have heq : insert a u ∪' t = u ∪' insert a t := by
      ext x
      constructor
      · intro hx
        rcases mem_funion.1 hx with h | h
        · rcases Finset.mem_insert.mp h with rfl | hu'
          · exact mem_funion.2 (Or.inr (Finset.mem_insert_self _ _))
          · exact mem_funion.2 (Or.inl hu')
        · exact mem_funion.2 (Or.inr (Finset.mem_insert_of_mem h))
      · intro hx
        rcases mem_funion.1 hx with hu' | h
        · exact mem_funion.2 (Or.inl (Finset.mem_insert_of_mem hu'))
        · rcases Finset.mem_insert.mp h with rfl | ht'
          · exact mem_funion.2 (Or.inl (Finset.mem_insert_self _ _))
          · exact mem_funion.2 (Or.inr ht')
    rwa [heq] at hunion

end InfoSys

end DomainTheory.InformationSystems
