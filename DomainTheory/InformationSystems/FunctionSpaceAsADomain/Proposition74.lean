module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.proposition_7_4_ii
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.proposition_7_4_iii
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.proposition_7_4_unique

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem theorem_74 :
    (∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (f : ApproximableMap A A),
      f.toElement (fixElement A f) = fixElement A f) ∧
    (∀ {α β : Type*} [DecidableEq α] [DecidableEq β]
      (A : InfoSys α) (B : InfoSys β)
      (f : ApproximableMap A A) (g : ApproximableMap B B) (h : ApproximableMap A B),
      comp h f = comp g h →
        h.toElement A.botElement = B.botElement →
          h.toElement (fixElement A f) = fixElement B g) ∧
    (∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (f : ApproximableMap A A) (φ : A.Element),
      f.toElement φ = φ →
        (∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) →
          φ = fixElement A f) :=
  ⟨@proposition_7_4_ii, @proposition_7_4_iii, @proposition_7_4_unique⟩

end DomainTheory.InformationSystems.InfoSys.ApproximableMap
