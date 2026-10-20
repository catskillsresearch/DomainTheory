module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The `∃/∀`-swap behind `mapOfSeq`: a single input neighbourhood `X ∈ x` works for all coordinates
iff each coordinate has its own (intersect the finitely many non-trivial ones). -/
theorem exists_forall_swap {x : V₀.Element} {W : Set (ℕ × β)}
    {g : ℕ → ApproximableMap V₀ V₁} (hW : (iterSys V₁).mem W) :
    (∃ X, x.mem X ∧ ∀ i, (g i).rel X (fiber W i)) ↔
      (∀ i, ∃ X, x.mem X ∧ (g i).rel X (fiber W i)) := by
  constructor
  · rintro ⟨X, hXx, hall⟩ i; exact ⟨X, hXx, hall i⟩
  · intro hall
    obtain ⟨N, hN⟩ := hW.2
    choose Xs hXx hXrel using hall
    have hbase : x.mem (V₀.interUpTo Xs N) := x.mem_interUpTo Xs (n := N) (fun i _ => hXx i)
    refine ⟨V₀.interUpTo Xs N, hbase, fun i => ?_⟩
    by_cases h : i < N
    · exact (g i).mono (hXrel i) (V₀.interUpTo_subset Xs h) subset_rfl (x.sub hbase)
        ((g i).rel_cod (hXrel i))
    · rw [hN i (not_lt.mp h)]; exact (g i).rel_master (x.sub hbase)

end DomainTheory.NeighbourhoodSystems
