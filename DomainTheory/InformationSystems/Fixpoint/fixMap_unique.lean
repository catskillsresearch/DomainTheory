/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Fixpoint.Basic
public import DomainTheory.InformationSystems.Fixpoint.fixElement_unique

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)














namespace ApproximableMap




/-- Uniqueness of `fix` as an approximable operator (Scott Thm 7.3). -/
theorem fixMap_unique (φ : ApproximableMap (functionSystem A A) A)
    (hpre : ∀ f : ApproximableMap A A,
      f.toElement (φ.toElement (approxMap_toElement A A f)) ≤
        φ.toElement (approxMap_toElement A A f))
    (hleast : ∀ f : ApproximableMap A A, ∀ x : A.Element,
      f.toElement x ≤ x → φ.toElement (approxMap_toElement A A f) ≤ x) :
    φ = fixMap A :=
  (ext_iff_toElement φ (fixMap A)).2 fun g => by
    let hf := element_toApproxMap A A g
    have hg : approxMap_toElement A A hf = g :=
      approxMap_toElement_element_toApproxMap A A g
    rw [← hg]
    exact fixElement_unique A hf (φ.toElement (approxMap_toElement A A hf))
      (hpre hf) (hleast hf)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
