module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.constMap
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56.comp_constMap

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem theorem_56 :
    (∀ {α β : Type*} [DecidableEq α] [DecidableEq β] {A : InfoSys α} {B : InfoSys β}
      (b : B.Element) (x : A.Element),
      (constMap (A := A) b).toElement x = b) ∧
    (∀ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}
      (f : ApproximableMap B C) (b : B.Element),
      comp f (constMap (A := A) b) = constMap (A := A) (f.toElement b)) ∧
    (∀ {α β δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq δ]
      {A : InfoSys α} {B : InfoSys β} {D : InfoSys δ}
      (b : B.Element) (g : ApproximableMap D A),
      comp (constMap (A := A) b) g = constMap (A := D) b) :=
  ⟨@constMap.toElement, @comp_constMap, @constMap.comp⟩

end DomainTheory.InformationSystems.InfoSys.ApproximableMap
