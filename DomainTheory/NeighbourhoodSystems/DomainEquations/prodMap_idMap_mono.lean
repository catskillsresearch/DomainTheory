module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `T(·) = (id_𝒟 × ·)` is monotone. -/
theorem prodMap_idMap_mono {γ : Type*} {E : NeighborhoodSystem γ}
    {f f' : ApproximableMap (iterSys V) E} (h : f ≤ f') :
    prodMap (idMap V) f ≤ prodMap (idMap V) f' := by
  intro W P hrel
  simp only [prodMap, paired_rel] at hrel ⊢
  exact ⟨hrel.1, hrel.2.1, comp_mono_gen h le_rfl _ _ hrel.2.2⟩

end Exercise618

end DomainTheory.NeighbourhoodSystems
