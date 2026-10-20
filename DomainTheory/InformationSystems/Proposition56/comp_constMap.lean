/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Proposition53
import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Proposition56.Basic
import DomainTheory.InformationSystems.Proposition56.constMap_toElement


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
