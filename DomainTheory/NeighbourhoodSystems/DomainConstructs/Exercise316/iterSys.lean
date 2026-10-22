module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The infinite iterate `𝒟^∞` over `Δ^∞ = ℕ × Δ`:
`W ∈ 𝒟^∞` iff every fiber is a neighbourhood of `𝒟` and all but finitely many fibers equal `Δ`. -/
def iterSys (V : NeighborhoodSystem α) : NeighborhoodSystem (ℕ × α) where
  mem W := (∀ i, V.mem (fiber W i)) ∧ ∃ N, ∀ i, N ≤ i → fiber W i = V.master
  master := {p | p.2 ∈ V.master}
  master_nonempty := by
    obtain ⟨a, ha⟩ := V.master_nonempty
    exact ⟨(0, a), ha⟩
  master_mem := ⟨fun _ => V.master_mem, 0, fun _ _ => rfl⟩
  inter_mem := by
    rintro W W' Z ⟨hWf, NW, hNW⟩ ⟨hW'f, NW', hNW'⟩ ⟨hZf, _⟩ hsub
    refine ⟨fun i => ?_, max NW NW', fun i hi => ?_⟩
    · rw [fiber_inter]
      exact V.inter_mem (hWf i) (hW'f i) (hZf i) (fiber_mono hsub i)
    · rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
        hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
  sub_master := by
    rintro W ⟨hWf, _⟩ ⟨i, a⟩ ha
    exact V.sub_master (hWf i) ha

end DomainTheory.NeighbourhoodSystems
