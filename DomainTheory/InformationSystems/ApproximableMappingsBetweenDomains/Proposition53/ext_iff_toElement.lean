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
