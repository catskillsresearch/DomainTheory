module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition67
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem616.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w


/-- **The per-step computation of Theorem 6.9's operator.** For the operator `Op = (k ∘ · ∘ j) ∘ Φ`
on the strict function space, `Op(x)` is the strict map `k ∘ T(toStrictMap x) ∘ j`. This is the
content of `homOp_apply_filter` plus the defining property `hΦ` of the Definition 6.8 witness `Φ`. -/
theorem opStep (T : Endofunctor DomainObj.{w}) (D E : DomainObj.{w})
    (j : ApproximableMap D.sys (T.obj D).sys) (k : ApproximableMap (T.obj E).sys E.sys)
    (hj : IsStrict j) (hk : IsStrict k)
    (Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys))
    (hΦ : ∀ f : StrictMap D.sys E.sys,
      (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1)
    (x : (strictFun D.sys E.sys).Element) :
    (toStrictMap (((homOp T D E j k hj hk).comp Φ).toElementMap x)).1
      = k.comp ((T.map (X := D) (Y := E) (toStrictMap x).1).comp j) := by
  set h := toStrictMap x with hh
  have hx : toStrictFilter h = x := toStrictFilter_toStrictMap x
  have hφ : Φ.toElementMap x
      = toStrictFilter (toStrictMap (Φ.toElementMap (toStrictFilter h))) := by
    rw [← hx]; exact (toStrictFilter_toStrictMap _).symm
  rw [toElementMap_comp, hφ, homOp_apply_filter, toStrictMap_toStrictFilter]
  show k.comp ((toStrictMap (Φ.toElementMap (toStrictFilter h))).1.comp j)
      = k.comp ((T.map (X := D) (Y := E) h.1).comp j)
  rw [hΦ h]

end DomainTheory.NeighbourhoodSystems
