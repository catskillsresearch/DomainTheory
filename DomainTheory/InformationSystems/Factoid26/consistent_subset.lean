/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.Factoid26.Token
public import DomainTheory.InformationSystems.Factoid26.Consistent

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid26

theorem consistent_subset {A B : Type*} {u v : Finset (Token A B)} (huv : v ⊆ u)
    (hu : Consistent u) : Consistent v :=
  fun _a _b _b' hb hb' => hu (huv hb) (huv hb')

end Factoid26

end DomainTheory.InformationSystems
