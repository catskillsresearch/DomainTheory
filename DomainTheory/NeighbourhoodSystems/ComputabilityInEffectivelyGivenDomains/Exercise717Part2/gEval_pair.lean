/-ai
The evaluator at the pair of an index and a certificate equals the certificate step applied to that combined code together with the memo table of the step at that code.

This is the defining equation of the course-of-values iteration.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


theorem gEval_pair (n cert : ℕ) :
    gEval fe fU fV mIdx (Nat.pair n cert)
      = gStep fe fU fV mIdx
          (Nat.pair (Nat.pair n cert) (rtbl (gStep fe fU fV mIdx) (Nat.pair n cert))) := by
  rw [gEval, gOf_def]

end Computability
end Exercise717
end DomainTheory.NeighbourhoodSystems
