module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem retract_isGraph {a : Pomega} (ha : Retract a) : graph (funOf a) = a := by
  apply subset_antisymm
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    have ha' : a = graph (fun x => funOf a (funOf a x)) := ha.out
    have : m ∈ funOf a (funOf a (e n)) := by
      simpa [retract_app ha] using hm
    rw [ha']
    exact ⟨n, m, rfl, this⟩
  · exact theorem_1_2.ii a

end DomainTheory.DataTypesAsLattices
