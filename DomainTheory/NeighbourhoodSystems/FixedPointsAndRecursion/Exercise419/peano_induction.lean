module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic

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
