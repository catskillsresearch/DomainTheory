module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.Basic
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.constMap

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
    rw [comp.toElement, constMap.toElement, constMap.toElement]

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
