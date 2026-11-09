module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_fixed
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_le_of_pre_fixed
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixMap_unique

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

theorem theorem_7_3 :
    (∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (f : ApproximableMap A A),
      f.toElement (fixElement A f) = fixElement A f) ∧
    (∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (f : ApproximableMap A A)
      (x : A.Element), f.toElement x ≤ x → fixElement A f ≤ x) ∧
    (∀ {α : Type*} [DecidableEq α] (A : InfoSys α)
      (φ : ApproximableMap (functionSystem A A) A),
      (∀ f : ApproximableMap A A,
        f.toElement (φ.toElement (approxMap_toElement A A f)) ≤
          φ.toElement (approxMap_toElement A A f)) →
      (∀ f : ApproximableMap A A, ∀ x : A.Element,
        f.toElement x ≤ x → φ.toElement (approxMap_toElement A A f) ≤ x) →
          φ = fixMap A) :=
  ⟨@fixElement_fixed, @fixElement_le_of_pre_fixed, @fixMap_unique⟩

end DomainTheory.InformationSystems.InfoSys.ApproximableMap
