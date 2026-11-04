module

public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.HF
public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.Hops
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep
public import DomainTheory.DataTypesAsLattices.Enumeration.PairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.tagInj
public import DomainTheory.DataTypesAsLattices.Retracts.seq4
public import DomainTheory.DataTypesAsLattices.Retracts.updateEnv
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
    simp only [hSucc, hApply, expPayload, tagInj.one]
    rw [ih]
    rfl
  | pred τ ih =>
    intro t
    rw [app2, encodeExp, Hstep.tag3]
    simp only [hPred, hApply, expPayload, tagInj.one]
    rw [ih]
    rfl
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    intro t
    rw [app2, encodeExp, Hstep.tag4]
    simp only [hCond, hApply, expPayload, tagInj.one, seq4.zero,
      seq4.one, seq4.two, seq4.three]
    rw [ihθ, ihτ, ihσ, ihρ]
    rfl
  | app τ σ ihτ ihσ =>
    intro t
    rw [app2, encodeExp, Hstep.tag5]
    simp only [hApp, hApply, expPayload, tagInj.one, PairSeq.app_zero,
      PairSeq.app_one]
    rw [ihτ, ihσ]
    rfl
  | lam n τ ih =>
    intro t
    rw [app2, encodeExp, Hstep.tag6]
    simp only [hLam, hApply, expPayload, tagInj.one, PairSeq.app_zero,
      PairSeq.app_one, updateEnv.ofNat]
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
