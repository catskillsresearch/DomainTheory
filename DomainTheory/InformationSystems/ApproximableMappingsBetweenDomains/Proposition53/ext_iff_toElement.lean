/-ai
Proposition 5.3(ii) states that two approximable mappings are equal if and only if they give the same image to every element.

Equality of the mappings rewrites one image into the other. In the other direction, extensionality of the relation reduces equality to agreement of related pairs. Each direction of that agreement follows from the pointwise characterization of the order, because equal images make each mapping lie below the other and the order on elements is reflexive.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.Basic
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.le_iff_toElement_le

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {A : InfoSys α} {B : InfoSys β}



/-- **Proposition 5.3(ii).** `f = g` iff `f(x) = g(x)` for all elements `x`. -/
theorem ext_iff_toElement (f g : ApproximableMap A B) :
    f = g ↔ ∀ x : A.Element, f.toElement x = g.toElement x := by
  constructor
  · intro h x
    rw [h]
  · intro hpoint
    refine ApproximableMap.ext fun u v => ?_
    constructor
    · intro hrel
      exact (le_iff_toElement_le f g).2 (fun x => (hpoint x) ▸ le_rfl) hrel
    · intro hrel
      exact (le_iff_toElement_le g f).2 (fun x => (hpoint x).symm ▸ le_rfl) hrel

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
