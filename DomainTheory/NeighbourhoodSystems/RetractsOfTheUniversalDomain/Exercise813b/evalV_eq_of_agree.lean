/-ai
If two valuations agree on every variable occurring in a formula, they assign the formula the same truth value.

The proof is by induction on the formula. A variable is covered by the agreement hypothesis. Falsehood and truth are independent of the valuation. A negation follows from the inductive hypothesis. For a conjunction or a disjunction, the variables are a union, so each inductive hypothesis applies to the agreement restricted to that side.
ai-/
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
