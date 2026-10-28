module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_iSup
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInf_succ_iSup
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conj_iInfTerm_eq
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_monotone
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iSup₂_monotone_eq_diagonal
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitTopology
public import DomainTheory.ContinuousLattice.InverseLimits.embInf
public import DomainTheory.ContinuousLattice.InverseLimits.embInfFun
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_def
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap
public import DomainTheory.ContinuousLattice.ScottMaps.proposition_2_5
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

noncomputable def projInfInf : ScottMap (DInfFn D₀ j₀) (DInf D₀ j₀) :=
  ⨆ n, jInfTerm D₀ j₀ n

namespace projInfInf

theorem apply (f : DInfFn D₀ j₀) :
    projInfInf D₀ j₀ f = ⨆ n, jInfTerm D₀ j₀ n f := by
  show (sSup (Set.range (jInfTerm D₀ j₀)) : ScottMap _ _) f = _
  rw [ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
  rfl

theorem preservesDirectedSup :
    PreservesDirectedSup (projInfInf D₀ j₀ : DInfFn D₀ j₀ → DInf D₀ j₀) :=
  (proposition_2_5 _).mp (projInfInf D₀ j₀).continuous

theorem embInfInf_eq (x : DInf D₀ j₀) :
    projInfInf D₀ j₀ (embInfInf D₀ j₀ x) = ⨆ n, embInf (towerType D₀) (towerProj D₀ j₀) (n + 1) (x.1 (n + 1)) := by
  rw [apply]
  set g := fun n m =>
    embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
      (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
               (embInf (towerType D₀) (towerProj D₀ j₀) n)
               (iInfTerm D₀ j₀ m x)) with hg
  have hmono (n : ℕ) : Monotone (fun m =>
      conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
              (embInf (towerType D₀) (towerProj D₀ j₀) n)
              (iInfTerm D₀ j₀ m x)) := fun a b hab =>
    (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
             (embInf (towerType D₀) (towerProj D₀ j₀) n)).monotone
      (ScottMap.le_def.mpr (iInfTerm_monotone D₀ j₀ x hab))
  have hinner (n : ℕ) : jInfTerm D₀ j₀ n (embInfInf D₀ j₀ x) = ⨆ m, g n m :=
    calc jInfTerm D₀ j₀ n (embInfInf D₀ j₀ x)
        = embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
            (⨆ m, conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                          (embInf (towerType D₀) (towerProj D₀ j₀) n)
                          (iInfTerm D₀ j₀ m x)) := by
          rw [jInfTerm.apply, embInfInf.apply,
            conjMap_iSup D₀ j₀ n (projInf (towerType D₀) (towerProj D₀ j₀) n)
              (embInf (towerType D₀) (towerProj D₀ j₀) n)
              (fun m => iInfTerm D₀ j₀ m x) (iInfTerm_monotone D₀ j₀ x)]
          rfl
      _ = ⨆ m, embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
              (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                       (embInf (towerType D₀) (towerProj D₀ j₀) n)
                       (iInfTerm D₀ j₀ m x)) :=
          embInf_succ_iSup D₀ j₀ n _ (hmono n)
      _ = ⨆ m, g n m := by simp only [hg]
  have g_mono_m (n : ℕ) : Monotone (g n) := by
    intro a b hab
    rw [hg]
    exact (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)).monotone
      ((conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                 (embInf (towerType D₀) (towerProj D₀ j₀) n)).monotone
        (ScottMap.le_def.mpr (iInfTerm_monotone D₀ j₀ x hab)))
  have g_mono_n_succ (m n : ℕ) : g n m ≤ g (n + 1) m := by
    rw [hg]
    dsimp only
    rw [← embInf_succ (towerType D₀) (towerProj D₀ j₀) (n + 1)
        (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                 (embInf (towerType D₀) (towerProj D₀ j₀) n)
                 (iInfTerm D₀ j₀ m x))]
    exact embInf_monotone (towerType D₀) (towerProj D₀ j₀) (n + 2)
      (conjMap_incl_le_conjMap_succ D₀ j₀ n (iInfTerm D₀ j₀ m x))
  have g_mono_n (m : ℕ) : Monotone (fun n => g n m) :=
    monotone_nat_of_le_succ (g_mono_n_succ m)
  have hin : (⨆ n, jInfTerm D₀ j₀ n (embInfInf D₀ j₀ x)) = ⨆ n, ⨆ m, g n m := by
    congr 1
    funext n
    exact hinner n
  rw [hin, iSup₂_monotone_eq_diagonal g g_mono_m g_mono_n]
  congr 1
  funext n
  rw [hg]
  dsimp only
  rw [conj_iInfTerm_eq D₀ j₀ n x]

theorem comp_embInfInf :
    (projInfInf D₀ j₀).comp (embInfInf D₀ j₀) = ScottMap.idMap := by
  apply ScottMap.ext
  intro x
  have hmono : Monotone (fun k => embInf (towerType D₀) (towerProj D₀ j₀) k (x.1 k)) :=
    monotone_nat_of_le_succ (embInf_le_succ (towerType D₀) (towerProj D₀ j₀) x)
  rw [ScottMap.comp_apply, ScottMap.idMap_apply, embInfInf_eq D₀ j₀ x,
    Monotone.iSup_nat_add hmono 1]
  exact (inverseLimit.eq_iSup (towerType D₀) (towerProj D₀ j₀) x).symm

theorem embInfInf (x : DInf D₀ j₀) :
    projInfInf D₀ j₀ (embInfInf D₀ j₀ x) = x := by
  have h := congrArg (fun g => g x) (comp_embInfInf D₀ j₀)
  simpa [ScottMap.comp_apply, ScottMap.idMap_apply] using h

end projInfInf

end LimitMaps

end DomainTheory.ContinuousLattice
