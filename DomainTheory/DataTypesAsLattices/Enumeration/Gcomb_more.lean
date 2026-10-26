module

public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack_ne_bot
public import DomainTheory.DataTypesAsLattices.Enumeration.not_mem_zero_Gcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack_combinatory
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_pos
public import DomainTheory.DataTypesAsLattices.Computability.combinatory_isRE

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

namespace Gcomb

theorem app_self : funOf Gcomb Gcomb = zeroC := by
  have hne : Gcomb ≠ botElem := by
    intro h
    have : Gpack = funOf botElem (ofNat 0) := by
      have := congrArg (fun w => funOf w (ofNat 0)) h
      simpa [zero] using this
    have hbot : funOf botElem (ofNat 0) = botElem := by
      ext; simp [funOf, botElem]
    exact Gpack_ne_bot (this.trans hbot)
  rw [app]
  exact eq_2_7_pos Gpack zeroC Gcomb not_mem_zero_Gcomb hne

theorem combinatory : IsCombinatory Gcomb := by
  simpa [eq_condC] using
    IsCombinatory.app (IsCombinatory.app IsCombinatory.cond Gpack_combinatory)
      IsCombinatory.zero

theorem isRE : IsRE Gcomb :=
  combinatory_isRE combinatory

end Gcomb

end DomainTheory.DataTypesAsLattices
