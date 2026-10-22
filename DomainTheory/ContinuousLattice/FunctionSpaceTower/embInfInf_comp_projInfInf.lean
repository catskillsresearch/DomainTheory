module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.embInfInf_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.projInfInf_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iSup₂_monotone_eq_diagonal
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj_retr_conjMap_succ

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44b

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- **Scott 1972, §4 (Theorem 4.4, second half).** `i_∞ ∘ j_∞ = id` on `[D_∞ → D_∞]`. -/
theorem embInfInf_comp_projInfInf :
    (embInfInf D₀ j₀).comp (projInfInf D₀ j₀) = ScottMap.idMap := by
  apply ScottMap.ext
  intro f
  rw [ScottMap.comp_apply, ScottMap.idMap_apply]
  apply ScottMap.ext
  intro z
  -- `rₙ = i_{n∞} ∘ j_{∞n}`, the Proposition-4.2 approximation of the identity on `D_∞`.
  set r : ℕ → ScottMap (DInf D₀ j₀) (DInf D₀ j₀) :=
    fun n => (embInf (towerType D₀) (towerProj D₀ j₀) n).comp
              (projInf (towerType D₀) (towerProj D₀ j₀) n) with hr
  have hrw : ∀ n (w : DInf D₀ j₀), r n w
      = embInf (towerType D₀) (towerProj D₀ j₀) n
          (projInf (towerType D₀) (towerProj D₀ j₀) n w) := by
    intro n w
    simp only [hr, ScottMap.comp_apply]
  have hr_mono : ∀ (w : DInf D₀ j₀), Monotone (fun m => r m w) := by
    intro w
    refine monotone_nat_of_le_succ (fun m => ?_)
    show r m w ≤ r (m + 1) w
    rw [hrw, hrw]
    exact embInf_le_succ (towerType D₀) (towerProj D₀ j₀) w m
  -- The functional equation `id = ⨆ₙ rₙ` (remark following Proposition 4.2), pointwise.
  have hA : ∀ (w : DInf D₀ j₀), w = ⨆ m, r m w := by
    intro w
    have h1 : (⨆ m, r m w)
        = ⨆ m, embInf (towerType D₀) (towerProj D₀ j₀) m
                (projInf (towerType D₀) (towerProj D₀ j₀) m w) :=
      iSup_congr (fun m => hrw m w)
    rw [h1]
    exact inverseLimit_eq_iSup (towerType D₀) (towerProj D₀ j₀) w
  -- Evaluating a supremum of Scott maps `D_∞ → D_∞` at a point is pointwise.
  have hsup_apply : ∀ (g : ℕ → ScottMap (DInf D₀ j₀) (DInf D₀ j₀)) (w : DInf D₀ j₀),
      (⨆ n, g n) w = ⨆ n, g n w := by
    intro g w
    rw [show (⨆ n, g n) = sSup (Set.range g) from sSup_range.symm,
      ScottMap.sSup_apply, ← Set.range_comp, sSup_range]
    rfl
  -- A Scott map commutes with a monotone `ℕ`-indexed supremum.
  have hcont : ∀ (g : ScottMap (DInf D₀ j₀) (DInf D₀ j₀)) (a : ℕ → DInf D₀ j₀),
      Monotone a → g (⨆ m, a m) = ⨆ m, g (a m) := by
    intro g a ha
    have hdir : DirectedOn (· ≤ ·) (Set.range a) :=
      directedOn_range.2 fun i j => ⟨max i j, ha (le_max_left i j), ha (le_max_right i j)⟩
    rw [show (⨆ m, a m) = sSup (Set.range a) from sSup_range.symm,
      g.preservesDirectedSup_coe (Set.range a) (Set.range_nonempty a) hdir,
      ← Set.range_comp, sSup_range]
    rfl
  -- `j_∞(f) = ⨆ₖ i_{(k+1)∞}(j_{∞k} ∘ f ∘ i_{k∞})`.
  have hpi : projInfInf D₀ j₀ f
      = ⨆ k, embInf (towerType D₀) (towerProj D₀ j₀) (k + 1)
          (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) k)
                   (embInf (towerType D₀) (towerProj D₀ j₀) k) f) := by
    rw [projInfInf_apply]
    exact iSup_congr (fun n => jInfTerm_apply D₀ j₀ n f)
  -- Lemma 4.5: the `(n+1)`-st component of `j_∞(f)` is the restriction `j_{∞n} ∘ f ∘ i_{n∞}`.
  have hcoord : ∀ n, (projInfInf D₀ j₀ f).1 (n + 1)
      = conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                (embInf (towerType D₀) (towerProj D₀ j₀) n) f := by
    intro n
    rw [hpi]
    exact lemma_4_5 (towerType D₀) (towerProj D₀ j₀)
      (fun k => conjMap (projInf (towerType D₀) (towerProj D₀ j₀) k)
                        (embInf (towerType D₀) (towerProj D₀ j₀) k) f)
      (fun m => towerProj_retr_conjMap_succ D₀ j₀ m f) n
  -- Evaluate `i_∞(j_∞(f))` pointwise as a sup of summands.
  have hev : embInfInf D₀ j₀ (projInfInf D₀ j₀ f) z
      = ⨆ n, (iInfTerm D₀ j₀ n (projInfInf D₀ j₀ f)) z := by
    rw [embInfInf_apply]
    exact hsup_apply (fun n => iInfTerm D₀ j₀ n (projInfInf D₀ j₀ f)) z
  -- Each summand is `rₙ (f (rₙ z))` (using `hcoord` and `conjMap`).
  have hterm : ∀ n, (iInfTerm D₀ j₀ n (projInfInf D₀ j₀ f)) z = r n (f (r n z)) := by
    intro n
    rw [hrw, hrw, iInfTerm_apply, hcoord n]
    rfl
  have hmono_frz : Monotone (fun m => f (r m z)) :=
    fun a b hab => f.monotone (hr_mono z hab)
  have hfm : ∀ n, Monotone (fun m => r n (f (r m z))) :=
    fun n _ _ hab => (r n).monotone (f.monotone (hr_mono z hab))
  have hfn : ∀ m, Monotone (fun n => r n (f (r m z))) :=
    fun m => hr_mono (f (r m z))
  -- The analytic step (Scott ~1326–1334): confine the lub via continuity of `f`, then collapse the
  -- monotone double sup to its diagonal.
  have hfz : f z = ⨆ n, r n (f (r n z)) :=
    calc f z = ⨆ k, r k (f z) := hA (f z)
      _ = ⨆ k, r k (f (⨆ m, r m z)) := by
            refine iSup_congr (fun k => ?_)
            rw [← hA z]
      _ = ⨆ k, r k (⨆ m, f (r m z)) := by
            refine iSup_congr (fun k => ?_)
            rw [hcont f (fun m => r m z) (hr_mono z)]
      _ = ⨆ k, ⨆ m, r k (f (r m z)) :=
            iSup_congr (fun k => hcont (r k) (fun m => f (r m z)) hmono_frz)
      _ = ⨆ n, r n (f (r n z)) :=
            iSup₂_monotone_eq_diagonal (fun n m => r n (f (r m z))) hfm hfn
  calc embInfInf D₀ j₀ (projInfInf D₀ j₀ f) z
      = ⨆ n, (iInfTerm D₀ j₀ n (projInfInf D₀ j₀ f)) z := hev
    _ = ⨆ n, r n (f (r n z)) := iSup_congr hterm
    _ = f z := hfz.symm

end Thm44b

end LimitMaps

end DomainTheory.ContinuousLattice
