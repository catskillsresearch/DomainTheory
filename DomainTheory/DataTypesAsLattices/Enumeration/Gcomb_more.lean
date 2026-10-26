module

public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Lambda.condC_more
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_bot
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.not_mem_zero_Gcomb
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_pos
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.combinatory_isRE

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace Gcomb

theorem eq_condC : Gcomb = funOf (funOf condC Gpack) zeroC :=
  (condC.beta2 Gpack zeroC).symm

theorem app (z : Pomega) :
    funOf Gcomb z = condSet z Gpack zeroC :=
  beta (condSet.isScottContinuous_left Gpack zeroC) z

theorem zero : funOf Gcomb (ofNat 0) = Gpack := by
  rw [app, eq_2_7_zero]

theorem bot : funOf Gcomb botElem = botElem := by
  rw [app, eq_2_7_bot]

theorem succ (k : ℕ) : funOf Gcomb (ofNat (k + 1)) = zeroC := by
  rw [app, eq_2_7_succ]

theorem combinatory : IsCombinatory Gcomb := by
  simpa [eq_condC] using
    IsCombinatory.app (IsCombinatory.app IsCombinatory.cond Gpack.combinatory)
      IsCombinatory.zero

theorem app_self : funOf Gcomb Gcomb = zeroC := by
  have hne : Gcomb ≠ botElem := by
    intro h
    have : Gpack = funOf botElem (ofNat 0) := by
      have := congrArg (fun w => funOf w (ofNat 0)) h
      simpa [zero] using this
    have hbot : funOf botElem (ofNat 0) = botElem := by
      ext; simp [funOf, botElem]
    exact Gpack.ne_bot (this.trans hbot)
  rw [app]
  exact eq_2_7_pos Gpack zeroC Gcomb not_mem_zero_Gcomb hne

theorem isRE : IsRE Gcomb :=
  combinatory_isRE combinatory

end Gcomb

end DomainTheory.DataTypesAsLattices
