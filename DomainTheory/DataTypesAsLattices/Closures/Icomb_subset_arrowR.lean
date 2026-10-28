
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Lambda.xi_star
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_1
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_11

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Icomb_subset_arrowR {a b : Pomega} (ha : Closure a) (hb : Closure b) :
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
    simp [comp.app]
  have hsub : e n ⊆ comp b (comp (e n) a) := by
    rw [← h3]; exact h1.trans h2
  exact ⟨n, m, rfl, hsub hm⟩

end DomainTheory.DataTypesAsLattices
