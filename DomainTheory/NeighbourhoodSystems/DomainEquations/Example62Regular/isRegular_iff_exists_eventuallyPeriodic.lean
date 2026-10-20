module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62Regular.eventuallyPeriodic_iff_isRegular

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Example62Regular

open Language

variable {n : ℕ}











/-- The inverse half of Scott's claim: **every regular event arises** as the language of an eventually
periodic tree. Concretely, take the tree whose root labels record membership in `L`; reading a tape
`σ` lands on the residual language `σ⁻¹ L`, of which there are finitely many exactly when `L` is
regular. -/
theorem isRegular_iff_exists_eventuallyPeriodic (L : Language (Fin n)) :
    L.IsRegular ↔ ∃ a : Tree n, EventuallyPeriodic a ∧ treeLang a = L := by
  classical
  constructor
  · intro hL
    refine ⟨fun σ => decide (σ ∈ L), ?_, ?_⟩
    · have hlang : treeLang (fun σ => decide (σ ∈ L)) = L := by
        ext σ; simp only [mem_treeLang, decide_eq_true_eq]
      rw [eventuallyPeriodic_iff_isRegular, hlang]; exact hL
    · ext σ; simp only [mem_treeLang, decide_eq_true_eq]
  · rintro ⟨a, hEP, rfl⟩
    exact (eventuallyPeriodic_iff_isRegular a).mp hEP

end Example62Regular
end DomainTheory.NeighbourhoodSystems
