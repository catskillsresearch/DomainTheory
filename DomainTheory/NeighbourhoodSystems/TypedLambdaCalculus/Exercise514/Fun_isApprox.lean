module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513


/-- Every `Fun u` is itself approximable, so `fun` really lands in the continuous maps. -/
theorem Fun_isApprox (u : Set ℕ) : IsApprox (Fun u) := by
  refine ⟨?_, ?_⟩
  · intro x x' hxx' m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    exact ⟨ns, fun n hn => hxx' (hsub n hn), htag⟩
  · intro x m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    exact ⟨ns, hsub, ns, fun n hn => hn, htag⟩

end DomainTheory.NeighbourhoodSystems.Exercise514
