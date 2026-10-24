module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.oneMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.oneDef
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.not_cone_subset_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_nil
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_false
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_true
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_bot_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.T
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation14
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation15
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.oneMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.oneMap_strBot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44


/-- **Exercise 4.19 — Peano (iii) for `{0,1}*`.** Induction: a predicate holding at `Λ` and closed
under both successors holds everywhere. (This is `List.rec`; it is the two-successor analogue of
Definition 4.5(iii) and the recursion engine behind `tail`/`empty`/`zero`/`one`.) -/
theorem peano_induction (P : Str → Prop) (hnil : P []) (hcons : ∀ b σ, P σ → P (b :: σ)) :
    ∀ σ, P σ := by
  intro σ
  induction σ with
  | nil => exact hnil
  | cons b σ ih => exact hcons b σ ih

end DomainTheory.NeighbourhoodSystems.Exercise419
