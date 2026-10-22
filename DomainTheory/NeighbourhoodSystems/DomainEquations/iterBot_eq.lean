module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `⊥` of `𝒟^∞` is the all-`⊥` sequence. -/
theorem iterBot_eq : (iterSys V).bot = ofSeq (fun _ : ℕ => V.bot) := by
  apply Element.ext
  intro W
  rw [mem_bot, mem_ofSeq]
  constructor
  · rintro rfl
    refine ⟨(iterSys V).master_mem, fun i => ?_⟩
    rw [fiber_iterSys_master, mem_bot]
  · rintro ⟨_, hfib⟩
    apply eq_of_fiber_eq
    intro i
    have hi := hfib i
    rw [fiber_iterSys_master]
    rwa [mem_bot] at hi

end Exercise618

end DomainTheory.NeighbourhoodSystems
