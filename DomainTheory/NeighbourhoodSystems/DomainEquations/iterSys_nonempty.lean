module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Exercise618

/-- The infinite iterate of an `∅`-free system is `∅`-free (each fibre is a non-empty neighbourhood). -/
theorem iterSys_nonempty {α : Type*} {V : NeighborhoodSystem α}
    (h : ∀ X, V.mem X → X.Nonempty) :
    ∀ W, (iterSys V).mem W → W.Nonempty := by
  rintro W ⟨hfib, _⟩
  obtain ⟨a, ha⟩ := h (fiber W 0) (hfib 0)
  exact ⟨(0, a), ha⟩

end Exercise618

end DomainTheory.NeighbourhoodSystems
