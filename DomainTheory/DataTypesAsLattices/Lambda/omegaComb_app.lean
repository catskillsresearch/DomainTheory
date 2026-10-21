/-ai
The omega combinator of u, applied to x, equals the application of u to the self-application of x.

The beta law applies, using Theorem 1.3 to compose continuity of application at u with continuity of diagonal application.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.diagApp_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices























theorem omegaComb_app (u x : Pomega) :
    funOf (omegaComb u) x = funOf u (funOf x x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) diagApp_isScottContinuous) x

end DomainTheory.DataTypesAsLattices
