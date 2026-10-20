/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Factoid34
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid84.Basic
import DomainTheory.InformationSystems.Factoid84.barElement_zero_eq_bot


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84




















theorem scottCon_empty_iff_consistent (r : ApproximableMap P P) :
    scottCon r ∅ ↔ ConsistentApprox r := by
  simp only [scottCon, ConsistentApprox, barElement_zero_eq_bot]
  rfl

end Factoid84
end DomainTheory.InformationSystems
