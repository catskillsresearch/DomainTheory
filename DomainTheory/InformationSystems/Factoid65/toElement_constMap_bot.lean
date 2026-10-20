/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Proposition56
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Factoid65.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}

/-- Elements of `|A|` are in bijection with approximable maps `1 → A` via `const`. -/
theorem toElement_constMap_bot (b : A.Element) :
    (constMap (A := unitSystem) b).toElement unitSystem.botElement = b :=
  constMap_toElement b unitSystem.botElement

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
