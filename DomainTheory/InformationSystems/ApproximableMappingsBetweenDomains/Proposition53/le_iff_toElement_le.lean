/-ai
Proposition 5.3(iii) states that one approximable mapping lies below another if and only if the image of every element under the first is contained in its image under the second.

If the relation of the first is contained in the relation of the second, a token of an image, witnessed by a related finite set, remains a token of the image under the second. Conversely, a related pair of consistent finite sets has the closure of the codomain set contained in the image of the closure of the domain set. The pointwise hypothesis and transitivity move that inclusion to the second mapping, and the converse of the closure bridge returns the relation.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.Basic
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
