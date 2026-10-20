module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1a.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `hX0`: index `0` presents `U`'s master neighbourhood. `decodeQPairList 0 = []`
(`decodeList_zero`), so `canonList` falls back to its `[(0,1)]` branch, which presents
`U.master` exactly as in `U_mem_presentedIntervals_canonList`. -/
theorem UX_zero : UX 0 = U.master := by
  rw [UX_eq]
  have hL : decodeQPairList 0 = [] := by
    unfold decodeQPairList; rw [decodeList_zero]; rfl
  rw [hL, canonList_eq_of_filter_eq_nil (by simp), presentedIntervals_cons, presentedIntervals_nil,
    Set.union_empty]
  rfl

end DomainTheory.NeighbourhoodSystems
