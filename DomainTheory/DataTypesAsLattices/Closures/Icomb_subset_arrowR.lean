module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_1
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_11

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, Theorem 5.3.** The function space of two closures is a
closure: it is a retract and contains `I`. -/
theorem Icomb_subset_arrowR {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ arrowR a b := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have h1 : e n ⊆ graph (fun x => funOf (e n) x) := eq_5_1 (e n)
  have h2 : graph (fun x => funOf (e n) x) ⊆
      graph (fun x => funOf b (funOf (e n) (funOf a x))) :=
    xi_star (fun x => eq_5_11 ha hb)
  have h3 :
      graph (fun x => funOf b (funOf (e n) (funOf a x))) =
        comp b (comp (e n) a) := by
    apply congrArg graph
    funext x
    simp [comp_app]
  have hsub : e n ⊆ comp b (comp (e n) a) := by
    rw [← h3]; exact h1.trans h2
  exact ⟨n, m, rfl, hsub hm⟩

end DomainTheory.DataTypesAsLattices
