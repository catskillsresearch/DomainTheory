module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v



/-- **Multiplicity, product case.** `embedFst`/`embedSnd` (hence the two projection pairs above)
are genuinely *different maps* as soon as `D` has an element `x ≠ ⊥`: evaluating both at `x` gives
`⟨x, ⊥⟩` vs. `⟨⊥, x⟩`, which differ in their first coordinate (`fst_pair`). -/
theorem embedFst_ne_embedSnd_of_ne_bot {α : Type u} {D : NeighborhoodSystem α} {x : D.Element}
    (hx : x ≠ D.bot) : embedFst D D ≠ embedSnd D D := fun h => hx <| by
  have heq := congrArg (fun f => f.toElementMap x) h
  simp only [embedFst, embedSnd, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap] at heq
  simpa using congrArg (·.fst) heq

end DomainTheory.NeighbourhoodSystems
