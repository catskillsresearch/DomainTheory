module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.vars

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

theorem evalV_eq_of_agree {φ : Formula} {v v' : ℕ → Bool} (h : ∀ i ∈ vars φ, v i = v' i) :
    evalV v φ = evalV v' φ := by
  induction φ with
  | var i => exact h i (Finset.mem_singleton_self i)
  | bot => rfl
  | top => rfl
  | neg φ ih => simp only [evalV, ih h]
  | and φ ψ ihφ ihψ =>
    simp only [evalV, vars] at h ⊢
    rw [ihφ (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihψ (fun i hi => h i (Finset.mem_union_right _ hi))]
  | or φ ψ ihφ ihψ =>
    simp only [evalV, vars] at h ⊢
    rw [ihφ (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihψ (fun i hi => h i (Finset.mem_union_right _ hi))]

end DomainTheory.NeighbourhoodSystems
