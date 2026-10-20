module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

theorem exists_inner_bound {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) :
    ∀ n, ∃ M, ∀ i, i < n → ∀ j, M ≤ j → fiber2 S i j = V.master := by
  intro n
  induction n with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨Mn, hMn⟩ := (hS.1 n).2
    refine ⟨max M Mn, fun i hi j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact hM i hlt j (le_trans (le_max_left _ _) hj)
    · subst heq
      exact hMn j (le_trans (le_max_right _ _) hj)

end Exercise718

end DomainTheory.NeighbourhoodSystems
