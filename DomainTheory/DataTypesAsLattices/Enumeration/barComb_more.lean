module

public import DomainTheory.DataTypesAsLattices.Enumeration.barComb
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_15
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepTerm_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepTerm
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_more
public import DomainTheory.DataTypesAsLattices.Enumeration.barStep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_combinatory
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_one

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

namespace barComb

theorem app2 (u x : Pomega) :
    funOf (funOf barComb u) x = barStepBody barComb u x := by
  have ha : funOf barComb u = graph (fun z => barStepBody barComb u z) :=
    _root_.DomainTheory.DataTypesAsLattices.eq_3_15 u
  rw [ha]
  exact beta (barStepBody.isScottContinuous_x barComb u) x

theorem combinatory : IsCombinatory barComb := by
  have hY : funOf Ycomb (interp barStepTerm (fun _ => botElem)) = barComb := by
    rw [barStepTerm_interp, theorem_2_5 barStep_isScottContinuous]
    rfl
  exact hY ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4.closed barStepTerm)

theorem on_R (u x : Pomega) :
    funOf (funOf barComb u) (funOf Rcomb x) =
      barPos u (funOf Rcomb x) := by
  rw [app2, barStepBody, Rcomb.app_zero, eq_2_7_zero]

theorem on_barPos_R (u v x : Pomega) :
    funOf (funOf barComb u) (barPos v (funOf Rcomb x)) =
      funOf (funOf barComb (funOf u v)) x := by
  rw [app2, barStepBody, barPos.zero, eq_2_7_succ,
    barPos.one, barPos.two, Rcomb.app, seq2_app_one]

end barComb

end DomainTheory.DataTypesAsLattices
