/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Fixpoint
import DomainTheory.InformationSystems.Proposition54
import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Proposition74.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)


/-- **Proposition 7.4.** Uniqueness via the Theorem 7.3 least-fixed-point property
(Plotkin’s (ii) is the fixed-point equation; leastness is 7.3(iii)). -/
theorem proposition_7_4_unique (f : ApproximableMap A A) (φ : A.Element)
    (hii : f.toElement φ = φ)
    (hleast : ∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) :
    φ = fixElement A f :=
  fixElement_unique A f φ (le_of_eq hii) hleast

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
