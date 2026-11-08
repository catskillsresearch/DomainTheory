module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.ext_iff_toElement
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.le_iff_toElement_le
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.rel_iff_closure_le

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem proposition_5_3 :
    (∀ {α β : Type*} [DecidableEq α] [DecidableEq β] {A : InfoSys α} {B : InfoSys β}
      (f g : ApproximableMap A B),
      f = g ↔ ∀ x : A.Element, f.toElement x = g.toElement x) ∧
    (∀ {α β : Type*} [DecidableEq α] [DecidableEq β] {A : InfoSys α} {B : InfoSys β}
      (f g : ApproximableMap A B),
      Le f g ↔ ∀ x : A.Element, f.toElement x ≤ g.toElement x) ∧
    (∀ {α β : Type*} [DecidableEq α] [DecidableEq β] {A : InfoSys α} {B : InfoSys β}
      (f : ApproximableMap A B) {u : Finset α} {v : Finset β}
      (hu : u ∈ A.Con) (hv : v ∈ B.Con),
      f.rel u v ↔ B.closure v hv ≤ f.toElement (A.closure u hu)) :=
  ⟨@ext_iff_toElement, @le_iff_toElement_le, @rel_iff_closure_le⟩

end DomainTheory.InformationSystems.InfoSys.ApproximableMap
