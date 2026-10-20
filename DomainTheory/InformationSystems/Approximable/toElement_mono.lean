/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Approximable.Basic


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
