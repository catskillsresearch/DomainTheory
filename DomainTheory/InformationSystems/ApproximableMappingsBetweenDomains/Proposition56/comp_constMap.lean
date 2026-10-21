/-ai
Proposition 5.6(ii) states that composing an approximable mapping after the constant mapping of a given value yields the constant mapping whose value is the image of that element.

Extensionality through images reduces the equality to an identity at each element. Rewriting by the action of composition and by the constant value of a constant mapping gives that identity.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.Basic
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.constMap_toElement

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β γ δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ} {D : InfoSys δ}


/-- **Proposition 5.6(ii).** `f ∘ (const b) = const (f(b))`. -/
theorem comp_constMap (f : ApproximableMap B C) (b : B.Element) :
    comp f (constMap (A := A) b) = constMap (A := A) (f.toElement b) :=
  (ext_iff_toElement _ _).2 fun x => by
    rw [comp_toElement, constMap_toElement, constMap_toElement]

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
