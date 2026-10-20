/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Product
import DomainTheory.InformationSystems.Factoid83.Basic
import DomainTheory.InformationSystems.Factoid83.uForgetFinset_empty


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

























































theorem UCon_empty : UCon (∅ : Finset UToken) := by
  simpa [UCon, uForgetFinset_empty] using not_VEnt_empty_top

end InfoSys
end DomainTheory.InformationSystems
