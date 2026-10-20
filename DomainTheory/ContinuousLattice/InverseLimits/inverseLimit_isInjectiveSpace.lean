module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_coordinate_continuous

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))



















/-- **Scott 1972, Proposition 4.1 (injectivity step).** Coordinatewise maximal extensions
assemble to an extension into the inverse limit. Lemma 3.9 is exactly what supplies compatibility
of adjacent coordinates. -/
theorem inverseLimit_isInjectiveSpace (hD : ∀ n, IsContinuousLattice (D n)) :
    @IsInjectiveSpace.{u, u} (InverseLimit D P) (inverseLimitTopology D P) := by
  intro X Y _ _ e he f
  let stageOrder : ∀ n, Preorder (D n) := fun _ => inferInstance
  let limitOrder : Preorder (InverseLimit D P) := inferInstance
  let : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : ∀ n, Preorder (D n) := stageOrder
  let : Preorder (InverseLimit D P) := limitOrder
  let fcoord (n : ℕ) (x : X) : D n := (f x).1 n
  have hfcoord (n : ℕ) : @Continuous X (D n) _ scottTopologicalSpace (fcoord n) :=
    (inverseLimit_coordinate_continuous D P n).comp f.continuous
  let fbar (n : ℕ) : Y → D n := scottExtend e (fcoord n)
  have hfbar_cont (n : ℕ) :
      @Continuous Y (D n) _ scottTopologicalSpace (fbar n) :=
    scottExtend_continuous (hD n) e (fcoord n)
  have hfbar_compat (y : Y) (n : ℕ) :
      (P n).retr (fbar (n + 1) y) = fbar n y := by
    symm
    exact lemma_3_9 (hD n) (hD (n + 1)) (P n) e he
      (hfcoord n) (hfcoord (n + 1)) (fun x => (f x).2 n |>.symm) y
  let fbarInf (y : Y) : InverseLimit D P :=
    ⟨fun n => fbar n y, hfbar_compat y⟩
  have hfbarInf_cont :
      @Continuous Y (InverseLimit D P) _ (inverseLimitTopology D P) fbarInf := by
    change @Continuous Y (InverseLimit D P) _
      (TopologicalSpace.induced (Subtype.val : InverseLimit D P → ∀ n, D n)
        (@Pi.topologicalSpace ℕ D (fun _ => scottTopologicalSpace))) fbarInf
    rw [continuous_induced_rng]
    exact continuous_pi hfbar_cont
  refine ⟨⟨fbarInf, hfbarInf_cont⟩, fun x => ?_⟩
  apply Subtype.ext
  funext n
  exact scottExtend_eq_of_continuous (hD n) e he (fcoord n) (hfcoord n) x

end InverseLimit
end DomainTheory.ContinuousLattice
