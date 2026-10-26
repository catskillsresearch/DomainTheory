module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
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
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_two
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_three
public import DomainTheory.DataTypesAsLattices.Functionality.updateEnvUnion_ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun_app2
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag0
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag1
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag2
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag3
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag4
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag5
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_tag6


@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hfun_interp : ∀ τ : LambTerm, ∀ t : Pomega,
    funOf (funOf Hfun (encodeExp τ)) t = Hinterp τ t := by
  intro τ
  induction τ with
  | var n =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep.tag0]
    rfl
  | zero =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep.tag1]
    rfl
  | succ τ ih =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep.tag2]
    simp only [hSucc, hApply, expPayload, tagInj_one]
    rw [ih]
    rfl
  | pred τ ih =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep.tag3]
    simp only [hPred, hApply, expPayload, tagInj_one]
    rw [ih]
    rfl
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep.tag4]
    simp only [hCond, hApply, expPayload, tagInj_one, seq4_app_zero,
      seq4_app_one, seq4_app_two, seq4_app_three]
    rw [ihθ, ihτ, ihσ, ihρ]
    rfl
  | app τ σ ihτ ihσ =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep.tag5]
    simp only [hApp, hApply, expPayload, tagInj_one, pairSeq_app_zero,
      pairSeq_app_one]
    rw [ihτ, ihσ]
    rfl
  | lam n τ ih =>
    intro t
    rw [Hfun_app2, encodeExp, Hstep.tag6]
    simp only [hLam, hApply, expPayload, tagInj_one, pairSeq_app_zero,
      pairSeq_app_one, updateEnvUnion_ofNat]
    congr 1
    apply congrArg graph
    funext x
    exact ih _

end DomainTheory.DataTypesAsLattices
