/-ai
Proposition 5.6(i) states that the constant mapping of value b sends every element to b.

A token of the image belongs to a finite set contained in b. Conversely, the empty set is contained in the element and is consistent, and the singleton of a token of b is contained in b.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β γ δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ} {D : InfoSys δ}


/-- **Proposition 5.6(i).** `(const b)(x) = b`. -/
theorem constMap_toElement (b : B.Element) (x : A.Element) :
    (constMap (A := A) b).toElement x = b := by
  apply le_antisymm
  · intro Y ⟨_u, _hu, ⟨_, hsub⟩⟩
    exact hsub (Finset.mem_coe.2 (Finset.mem_singleton_self Y))
  · intro Y hY
    refine ⟨∅, ?_, ?_⟩
    · intro a ha
      exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))
    · refine ⟨A.con_empty, ?_⟩
      intro Z hZ
      have hZ' : Z ∈ ({Y} : Finset β) := Finset.mem_coe.1 hZ
      rw [Finset.mem_singleton] at hZ'
      subst hZ'
      exact hY

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
