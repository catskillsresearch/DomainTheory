module

public import DomainTheory.BridgeTheorems.toFilter
public import DomainTheory.BridgeTheorems.ofFilter
public import DomainTheory.BridgeTheorems.mem_basicOpen_singleton
import DomainTheory.InformationSystems.ElementsOfASystem.closure

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem ofFilter_toFilter (x : A.Element) : ofFilter A (toFilter A x) = x := by
  have hc : (ofFilter A (toFilter A x)).carrier = x.carrier := by
    ext a
    constructor
    · intro ha
      obtain ⟨u, hu, heq, hsub⟩ := ha
      have huA : A.closure u hu ∈ A.basicOpen u := closure.subset A hu
      have hsing : A.closure u hu ∈ A.basicOpen ({a} : Finset α) := by
        rw [heq]; exact huA
      have ha' : a ∈ (A.closure u hu).carrier := (mem_basicOpen_singleton A).1 hsing
      exact x.closed u a hsub ha'
    · intro ha
      refine ⟨({a} : Finset α), A.con_sing a, rfl, ?_⟩
      intro c hc
      have hc' : c = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      exact hc' ▸ ha
  rcases x with ⟨c, cons, clo⟩
  rcases hte : ofFilter A (toFilter A ⟨c, cons, clo⟩) with ⟨c', cons', clo'⟩
  have hc' : c' = c := by simpa [hte] using hc
  subst hc'
  rfl

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
