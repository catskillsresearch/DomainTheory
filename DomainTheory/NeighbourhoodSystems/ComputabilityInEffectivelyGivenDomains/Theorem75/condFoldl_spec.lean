module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condSet_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condSet_subset
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condSet_cons_pos
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condSet_cons_neg

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- Correctness of the conditional `inter`-fold (`if`-form). When the running set is consistent, the
fold computes an index of it, by induction with `inter_spec` (mirrors `interFrom_eq_of_foldl`). -/
theorem condFoldl_spec (incl0 : ℕ → ℕ)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (k : ℕ) :
    ∀ (el : List ℕ) (A : Set β) (a : ℕ), P₁.X a = A → V₁.mem A →
      V₁.mem (condSet P₀ P₁ k A el) →
      P₁.X (List.foldl (fun acc x => if incl0 (Nat.pair k x.unpair.1) = 1
              then P₁.inter acc x.unpair.2 else acc) a el) = condSet P₀ P₁ k A el
  | [], A, a, hXa, _, _ => by rw [List.foldl_nil, condSet_nil]; exact hXa
  | e :: el, A, a, hXa, hA, hcons => by
    rw [List.foldl_cons]
    by_cases hpred : incl0 (Nat.pair k e.unpair.1) = 1
    · rw [ite_eq_left hpred]
      have hincl : P₀.X k ⊆ P₀.X e.unpair.1 := by
        have h := (hincl0 (Nat.pair k e.unpair.1)).mp hpred
        rwa [unpair_pair_fst, unpair_pair_snd] at h
      rw [condSet_cons_pos P₀ P₁ hincl] at hcons ⊢
      have hwit : V₁.mem (A ∩ P₁.X e.unpair.2) :=
        V₁.inter_mem hA (P₁.mem_X _) hcons (condSet_subset P₀ P₁ k (A ∩ P₁.X e.unpair.2) el)
      have hk : ∃ j, P₁.X j ⊆ P₁.X a ∩ P₁.X e.unpair.2 := by
        obtain ⟨j, hj⟩ := P₁.surj hwit; exact ⟨j, by rw [hj, hXa]⟩
      have hXinter : P₁.X (P₁.inter a e.unpair.2) = A ∩ P₁.X e.unpair.2 := by
        rw [P₁.inter_spec hk, hXa]
      exact condFoldl_spec incl0 hincl0 k el (A ∩ P₁.X e.unpair.2) (P₁.inter a e.unpair.2)
        hXinter hwit hcons
    · rw [ite_eq_right hpred]
      have hincl : ¬ P₀.X k ⊆ P₀.X e.unpair.1 := fun hc =>
        hpred ((hincl0 (Nat.pair k e.unpair.1)).mpr (by rwa [unpair_pair_fst, unpair_pair_snd]))
      rw [condSet_cons_neg P₀ P₁ hincl] at hcons ⊢
      exact condFoldl_spec incl0 hincl0 k el A a hXa hA hcons

end DomainTheory.NeighbourhoodSystems
