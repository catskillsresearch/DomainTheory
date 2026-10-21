/-ai
Scott 1976, Theorem 1.3, the substitution theorem. The composite of two Scott-continuous endomaps of Pω is Scott continuous.

The result is the composition case of the substitution theorem.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3_comp

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.3 (The substitution theorem).** Continuous
functions of several variables on `Pω` are closed under substitution. -/
theorem theorem_1_3 {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun x => f (g x)) :=
  theorem_1_3_comp hf hg

end DomainTheory.DataTypesAsLattices
