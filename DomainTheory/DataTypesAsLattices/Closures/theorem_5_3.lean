module

public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Closures.Closure
import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_arrowR
import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_3_more
import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_5_3 {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Retract (arrowR a b) := by
  constructor
  change arrowR a b = graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3.i ha.out.2 hb.out.2, arrowR.app]

namespace theorem_5_3

theorem closure {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Closure (arrowR a b) :=
  ⟨⟨Icomb_subset_arrowR ha hb, theorem_5_3 ha hb⟩⟩

end theorem_5_3

end DomainTheory.DataTypesAsLattices
