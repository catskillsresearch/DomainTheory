/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition56.Basic
public import DomainTheory.InformationSystems.Proposition56.constMap_toElement

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β γ δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ} {D : InfoSys δ}


/-- Uniqueness: any map with constant value `b` equals `const b`. -/
theorem constMap_unique (b : B.Element) (f : ApproximableMap A B)
    (h : ∀ x : A.Element, f.toElement x = b) :
    f = constMap (A := A) b :=
  (ext_iff_toElement f (constMap (A := A) b)).2 fun x => by
    rw [h x, constMap_toElement]

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
