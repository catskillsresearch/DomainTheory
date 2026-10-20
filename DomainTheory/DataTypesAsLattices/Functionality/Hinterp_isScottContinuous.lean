module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem Hinterp_isScottContinuous (τ : LambTerm) :
    IsScottContinuous (Hinterp τ) := by
  induction τ with
  | var n =>
    exact funOf_isScottContinuous_left (ofNat n)
  | zero =>
    exact const_isScottContinuous _
  | succ τ ih =>
    exact continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous whichC) ih)
      (theorem_1_3 (funOf_isScottContinuous inleftC)
        (theorem_1_3 succSet_isScottContinuous
          (theorem_1_3 (funOf_isScottContinuous outC) ih)))
      (const_isScottContinuous botElem)
  | pred τ ih =>
    exact continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous whichC) ih)
      (theorem_1_3 (funOf_isScottContinuous inleftC)
        (theorem_1_3 predSet_isScottContinuous
          (theorem_1_3 (funOf_isScottContinuous outC) ih)))
      (const_isScottContinuous botElem)
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    exact theorem_1_3 (f := funOf lambR)
      (g := fun t =>
        condSet (funOf whichC (Hinterp θ t))
          (condSet (funOf outC (Hinterp θ t)) (Hinterp τ t) (Hinterp σ t))
          (Hinterp ρ t))
      (funOf_isScottContinuous lambR)
      (continuous_nary
        (fun y z => condSet_isScottContinuous_left y z)
        (fun x z => condSet_isScottContinuous_mid x z)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (funOf_isScottContinuous whichC) ihθ)
        (continuous_nary
          (fun y z => condSet_isScottContinuous_left y z)
          (fun x z => condSet_isScottContinuous_mid x z)
          (fun x y => condSet_isScottContinuous_right x y)
          (theorem_1_3 (funOf_isScottContinuous outC) ihθ) ihτ ihσ)
        ihρ)
  | app τ σ ihτ ihσ =>
    exact continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous whichC) ihτ)
      (const_isScottContinuous botElem)
      (continuous_tuple
        (fun y => funOf_isScottContinuous_left y)
        (fun u => funOf_isScottContinuous u)
        (theorem_1_3 (funOf_isScottContinuous outC) ihτ) ihσ)
  | lam n τ ih =>
    exact theorem_1_3 (f := funOf inrightC)
      (g := fun t => graph (fun x => Hinterp τ (updateEnv t x n)))
      (funOf_isScottContinuous inrightC)
      (graph_const_isScottContinuous
        (fun t x => Hinterp τ (updateEnv t x n))
        (fun x => theorem_1_3 ih
          (graph_const_isScottContinuous
            (fun t m => if m = ofNat n then x else funOf t m)
            (fun m => by
              by_cases h : m = ofNat n
              · simpa [h] using const_isScottContinuous (c := x)
              · simpa [h] using funOf_isScottContinuous_left m))))

end DomainTheory.DataTypesAsLattices
