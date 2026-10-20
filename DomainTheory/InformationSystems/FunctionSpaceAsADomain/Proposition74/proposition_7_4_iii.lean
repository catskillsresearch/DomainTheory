/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.fixElement_le_toElement_fix
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.toElement_fix_le_fixElement

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)


/-- **Proposition 7.4(iii).** Naturality of `fix` for strict commuting maps. -/
theorem proposition_7_4_iii (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement) :
    h.toElement (fixElement A f) = fixElement B g := by
  apply le_antisymm
  · exact toElement_fix_le_fixElement A B f g h hcomm hstrict
  · exact fixElement_le_toElement_fix A B f g h hcomm

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
