/-ai
The closures of consistent finite sets contained in an element are directed.

The union of two such sets is still contained in the element, and it is consistent because it is a finite subset of the element. Each set is included in the union, so monotonicity of closure puts both closures below the closure of the union.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closure_le_of_subset

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- The family of finite approximations to `x` is directed under `≤`. -/
theorem closures_directed (x : sys.Element) {u v : Finset α}
    (hu : u ∈ sys.Con) (hv : v ∈ sys.Con)
    (huX : ↑u ⊆ x.carrier) (hvX : ↑v ⊆ x.carrier) :
    ∃ (w : Finset α) (hw : w ∈ sys.Con),
      ↑w ⊆ x.carrier ∧
        sys.closure u hu ≤ sys.closure w hw ∧
        sys.closure v hv ≤ sys.closure w hw := by
  let w := u ∪' v
  have hwX : ↑w ⊆ x.carrier := by
    intro a ha
    rcases mem_funion.1 (Finset.mem_coe.1 ha) with h | h
    · exact huX (Finset.mem_coe.2 h)
    · exact hvX (Finset.mem_coe.2 h)
  have hw : w ∈ sys.Con := x.consistent w hwX
  refine ⟨w, hw, hwX, ?_, ?_⟩
  · exact sys.closure_le_of_subset hu hw (subset_funion_left u v)
  · exact sys.closure_le_of_subset hv hw (subset_funion_right u v)

end InfoSys
end DomainTheory.InformationSystems
