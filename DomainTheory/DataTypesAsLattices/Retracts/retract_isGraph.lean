/-ai
A retract equals the graph of its own application.

A code pair in the graph has its value in the application to the corresponding finite set. The retract equation rewrites the retract as the graph of the double application, and idempotence puts the value in that double application, so the pair lies in the retract. The other inclusion is the second clause of Theorem 1.2.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem retract_isGraph {a : Pomega} (ha : IsRetract a) : graph (funOf a) = a := by
  apply subset_antisymm
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    have ha' : a = graph (fun x => funOf a (funOf a x)) := ha
    have : m ∈ funOf a (funOf a (e n)) := by
      simpa [retract_app ha] using hm
    rw [ha']
    exact ⟨n, m, rfl, this⟩
  · exact theorem_1_2_ii a

end DomainTheory.DataTypesAsLattices
