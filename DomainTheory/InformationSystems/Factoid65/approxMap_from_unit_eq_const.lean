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
public import DomainTheory.InformationSystems.Factoid65.unitElement_eq_bot

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}

/-- Every approximable map out of `1` is constant (Scott Factoid 6.5). -/
theorem approxMap_from_unit_eq_const (f : ApproximableMap unitSystem A) :
    f = constMap (A := unitSystem) (f.toElement unitSystem.botElement) :=
  constMap_unique (f.toElement unitSystem.botElement) f fun x => by
    rw [unitElement_eq_bot x]

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
