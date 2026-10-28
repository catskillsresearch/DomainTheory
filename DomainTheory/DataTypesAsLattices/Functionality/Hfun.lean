module

public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.HF
public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload
public import DomainTheory.DataTypesAsLattices.Functionality.hApply
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc
public import DomainTheory.DataTypesAsLattices.Functionality.hPred
public import DomainTheory.DataTypesAsLattices.Functionality.hCond
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Functionality.hLam
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Hfun : Pomega := fix HF

namespace Hfun

theorem fixed : HF Hfun = Hfun :=
  (theorem_1_4 HF.isScottContinuous).1

theorem app2 (e t : Pomega) :
    funOf (funOf Hfun e) t = Hstep Hfun e t := by
  have h := congrArg (fun H => funOf (funOf H e) t) fixed
  simpa [HF.app2] using h.symm

theorem interp : ∀ τ : LambTerm, ∀ t : Pomega,
    funOf (funOf Hfun (encodeExp τ)) t = Hinterp τ t := by
  intro τ
  induction τ with
  | var n =>
    intro t
    rw [app2, encodeExp, Hstep.tag0]
    rfl
  | zero =>
    intro t
    rw [app2, encodeExp, Hstep.tag1]
    rfl
  | succ τ ih =>
    intro t
    rw [app2, encodeExp, Hstep.tag2]
    simp only [hSucc, hApply, expPayload, tagInj_one]
    rw [ih]
    rfl
  | pred τ ih =>
    intro t
    rw [app2, encodeExp, Hstep.tag3]
    simp only [hPred, hApply, expPayload, tagInj_one]
    rw [ih]
    rfl
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    intro t
    rw [app2, encodeExp, Hstep.tag4]
    simp only [hCond, hApply, expPayload, tagInj_one, seq4_app.zero,
      seq4_app.one, seq4_app.two, seq4_app.three]
    rw [ihθ, ihτ, ihσ, ihρ]
    rfl
  | app τ σ ihτ ihσ =>
    intro t
    rw [app2, encodeExp, Hstep.tag5]
    simp only [hApp, hApply, expPayload, tagInj_one, pairSeq_app_zero,
      pairSeq_app_one]
    rw [ihτ, ihσ]
    rfl
  | lam n τ ih =>
    intro t
    rw [app2, encodeExp, Hstep.tag6]
    simp only [hLam, hApply, expPayload, tagInj_one, pairSeq_app_zero,
      pairSeq_app_one, updateEnvUnion.ofNat]
    congr 1
    apply congrArg graph
    funext x
    exact ih _

theorem decode (τ : LambTerm) :
    funOf Hfun (encodeExp τ) = graph (Hinterp τ) := by
  have hβ : funOf Hfun (encodeExp τ) = graph (fun t => Hstep Hfun (encodeExp τ) t) := by
    have := congrArg (fun H => funOf H (encodeExp τ)) fixed
    simpa [HF.app] using this.symm
  refine hβ.trans ?_
  apply congrArg graph
  funext t
  simpa [app2] using interp τ t

end Hfun

end DomainTheory.DataTypesAsLattices
