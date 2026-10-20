/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Factoid83.Basic
public import DomainTheory.InformationSystems.Factoid83.uForgetFinset_empty

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

























































theorem UCon_empty : UCon (∅ : Finset UToken) := by
  simpa [UCon, uForgetFinset_empty] using not_VEnt_empty_top

end InfoSys
end DomainTheory.InformationSystems
