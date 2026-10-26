module

public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_bot
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.intF
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.7).** Integer retract as the least fixed point. -/
def intR : Pomega := fix intF

namespace intR

theorem eq_intF : intF intR = intR :=
  (theorem_1_4 intF.isScottContinuous).1

theorem app (u : Pomega) :
    funOf intR u =
      dcondSet u (ofNat 0) (dcondSet (funOf intR (predSet u)) u u) := by
  have h := congrArg (fun a => funOf a u) eq_intF
  simpa [intF.app] using h.symm

theorem bot : funOf intR botElem = botElem := by
  rw [app, dcondSet.bot]

end intR

end DomainTheory.DataTypesAsLattices
