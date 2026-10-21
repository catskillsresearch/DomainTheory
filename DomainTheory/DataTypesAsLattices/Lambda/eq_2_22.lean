/-ai
Applying the cons sequence of x and xs to z yields the conditional z ⊃ x, xs(z − 1).

This is the beta law for the continuous body of that cons sequence.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seqCons_body

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































theorem eq_2_22 (x xs z : Pomega) :
    funOf (seqCons x xs) z = condSet z x (funOf xs (predSet z)) :=
  beta (seqCons_body x xs) z

end DomainTheory.DataTypesAsLattices
