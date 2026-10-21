/-ai
The primitive-recursion step of a base, a step, and a functional, applied to an argument, equals the conditional that returns the base on zero and otherwise applies the step and then the functional to the predecessor.

The beta law applies, using continuity of the step body in the argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.primRecStep_body_isScottContinuous_n

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem primRecStep_app (a f u n : Pomega) :
    funOf (primRecStep a f u) n =
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))) :=
  beta (primRecStep_body_isScottContinuous_n a f u) n

end DomainTheory.DataTypesAsLattices
