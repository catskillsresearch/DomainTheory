/-ai
For each u, the map sending t to the application of u to the successor of t is Scott continuous.

This is the substitution theorem applied to the continuity of application of u and the continuity of the successor.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem termShift_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun t => funOf u (succSet t)) :=
  theorem_1_3 (funOf_isScottContinuous u) succSet_isScottContinuous

end DomainTheory.DataTypesAsLattices
