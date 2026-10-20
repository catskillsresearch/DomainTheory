/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Factoid34
public import DomainTheory.InformationSystems.Factoid35
public import DomainTheory.InformationSystems.Factoid84.PEnt
public import DomainTheory.InformationSystems.Factoid84.P
public import DomainTheory.InformationSystems.Factoid84.bar
public import DomainTheory.InformationSystems.Factoid84.barElement
public import DomainTheory.InformationSystems.Factoid84.botElement
public import DomainTheory.InformationSystems.Factoid84.topElement
public import DomainTheory.InformationSystems.Factoid84.ReflApprox
public import DomainTheory.InformationSystems.Factoid84.IdemApprox
public import DomainTheory.InformationSystems.Factoid84.BotApprox
public import DomainTheory.InformationSystems.Factoid84.RogueApprox
public import DomainTheory.InformationSystems.Factoid84.ConsistentApprox
public import DomainTheory.InformationSystems.Factoid84.P_AllConsistent

@[expose] public section

namespace DomainTheory.InformationSystems
namespace Factoid84

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap













/-- Scott (1)–(5): approximable maps that present entailment relations / domains. -/
structure IsDomainApprox (r : ApproximableMap P P) : Prop where
  refl : ReflApprox r
  idem : IdemApprox r
  bot : BotApprox r
  rogue : RogueApprox r
  consistent : ConsistentApprox r

end Factoid84
end DomainTheory.InformationSystems
