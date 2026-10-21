/-ai
The image of an element under an approximable mapping is monotone.

A token of the image is witnessed by a finite set contained in the element and related to the singleton of that token. The same finite set is contained in any larger element, so the token belongs to the image of the larger element.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]


namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}


theorem toElement_mono (f : ApproximableMap A B) {x y : A.Element} (hxy : x ≤ y) :
    f.toElement x ≤ f.toElement y := by
  intro Y ⟨u, hu, hrel⟩
  exact ⟨u, fun z hz => hxy (hu hz), hrel⟩

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
