/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Order.Hom.Basic
import Mathlib.Order.Sum.Order
import Mathlib.Order.WithBot
import DomainTheory.InformationSystems.Theorem72
import DomainTheory.InformationSystems.Proposition64
import DomainTheory.BridgeTheorems.InfoSysConstructions.Basic


namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)





theorem unpair_mono {z₁ z₂ : (productSystem A B).Element} (hz : z₁ ≤ z₂) :
    unpair A B z₁ ≤ unpair A B z₂ := by
  constructor
  · exact (fstMap A B).toElement_mono hz
  · exact (sndMap A B).toElement_mono hz

end InfoSysConstructions
end DomainTheory.BridgeTheorems
