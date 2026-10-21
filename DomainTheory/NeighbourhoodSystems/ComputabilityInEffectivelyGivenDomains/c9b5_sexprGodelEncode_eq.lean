/-ai
The c9b5 Gödel encoding of an S-expression equals the encoding of the expression.

Induct on the expression. The sigma case is reflexivity. A singleton simplifies by the equality of the boolean-list encodings. Concatenation and intersection simplify by the inductive hypotheses on the two subexpressions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.c9b5_encodeListBool_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem c9b5_sexprGodelEncode_eq (e : SExpr) :
    Domain.Recursive.c9b5_sexprGodelEncode e = SExpr.encode e := by
  induction e with
  | sigma => rfl
  | single σ => simp [Domain.Recursive.c9b5_sexprGodelEncode, SExpr.encode, c9b5_encodeListBool_eq]
  | cat a b iha ihb => simp [Domain.Recursive.c9b5_sexprGodelEncode, SExpr.encode, iha, ihb]
  | cap a b iha ihb => simp [Domain.Recursive.c9b5_sexprGodelEncode, SExpr.encode, iha, ihb]

end Exercise722

end DomainTheory.NeighbourhoodSystems
