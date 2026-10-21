/-ai
For a code strictly below another, the memo table of the certificate step at the larger code stores, at the corresponding earlier position, the value of the evaluator at the smaller code.

This is the memo-table lookup law for the course-of-values iteration, applied to the certificate step.
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



/-- Memo lookup, in `gEval` form: at any earlier code `w' < w`, position `w-1-w'` of the table is
`gEval w'`. -/
theorem listGet_rtbl_gEval {w' w : ℕ} (h : w' < w) :
    listGet (rtbl (gStep fe fU fV mIdx) w) (w - 1 - w') = gEval fe fU fV mIdx w' :=
  listGet_rtbl (gStep fe fU fV mIdx) h

end Computability
end Exercise717
end DomainTheory.NeighbourhoodSystems
