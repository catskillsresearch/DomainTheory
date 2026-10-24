module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.Le
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.rel_iff_closure_le

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {A : InfoSys α} {B : InfoSys β}


/-- **Proposition 5.3(iii).** `f ⊆ g` iff `f(x) ⊆ g(x)` for all elements `x`. -/
theorem le_iff_toElement_le (f g : ApproximableMap A B) :
    Le f g ↔ ∀ x : A.Element, f.toElement x ≤ g.toElement x := by
  constructor
  · intro hfg x Y ⟨u, hu, hrel⟩
    exact ⟨u, hu, hfg hrel⟩
  · intro hpoint u v hrel
    have hu : u ∈ A.Con := f.rel_dom hrel
    have hv : v ∈ B.Con := f.rel_cod hrel
    have hbridge : B.closure v hv ≤ f.toElement (A.closure u hu) :=
      (f.rel_iff_closure_le hu hv).1 hrel
    have hsub : B.closure v hv ≤ g.toElement (A.closure u hu) :=
      le_trans hbridge (hpoint (A.closure u hu))
    exact (g.rel_iff_closure_le hu hv).2 hsub

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
