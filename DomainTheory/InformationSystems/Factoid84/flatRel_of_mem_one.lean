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


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84
























theorem flatRel_of_mem_one {u v : Finset ℕ} (h : 1 ∈ u) : flatRel u v :=
  Or.inl h

end Factoid84
end DomainTheory.InformationSystems
