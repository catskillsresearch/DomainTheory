module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u





/-- A functor continuous on maps **preserves strictness** (so it genuinely lives on Scott's category
of domains and strict maps): if `f` is strict then so is `T(f)`. This is automatic from the witnessing
equation, whose left-hand side is the underlying map of a `StrictMap`. -/
theorem ContinuousOnMaps.isStrict_map {T : Endofunctor DomainObj} (h : ContinuousOnMaps T)
    {D E : DomainObj} (f : StrictMap D.sys E.sys) :
    IsStrict (T.map (X := D) (Y := E) f.1) := by
  obtain ⟨Φ, hΦ⟩ := h D E
  rw [← hΦ f]
  exact (toStrictMap (Φ.toElementMap (toStrictFilter f))).2

end DomainTheory.NeighbourhoodSystems
