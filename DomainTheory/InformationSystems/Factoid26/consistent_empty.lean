/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.Factoid26.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace Factoid26



theorem consistent_empty {A B : Type*} :
    Consistent (∅ : Finset (Token A B)) := by
  intro _a _b _b' hb _
  exact False.elim (Finset.notMem_empty _ hb)

end Factoid26
end DomainTheory.InformationSystems
