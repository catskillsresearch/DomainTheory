/-ai
Proposition 5.4(ii) states that the identity approximable mapping sends every element to itself.

If a token lies in the image, it is entailed by a finite set contained in the element, so closure of the element contains the token. Conversely, the singleton of a token of the element is contained in the element, and reflexivity of entailment relates that singleton to itself.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


/-- **Proposition 5.4(ii).** `I_A(x) = x`. -/
theorem idMap_toElement (x : A.Element) : (idMap A).toElement x = x := by
  apply le_antisymm
  · intro Y ⟨u, hu, hrel⟩
    -- hrel.2.2 : EntSet u {Y}, so Ent u Y
    have hEnt : A.Ent u Y := hrel.2.2 Y (Finset.mem_singleton_self Y)
    exact x.closed u Y hu hEnt
  · intro Y hY
    refine ⟨{Y}, ?_, ?_⟩
    · intro z hz
      have hz' : z ∈ ({Y} : Finset α) := Finset.mem_coe.1 hz
      rw [Finset.mem_singleton] at hz'
      rw [hz']
      exact hY
    · refine ⟨A.con_sing Y, A.con_sing Y, ?_⟩
      exact proposition_2_3_iii A (A.con_sing Y)

end InfoSys
end DomainTheory.InformationSystems
