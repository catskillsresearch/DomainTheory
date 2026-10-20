/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.BridgeTheorems.InfoSysConstructions
public import DomainTheory.BridgeTheorems.PresentationDomains
public import DomainTheory.BridgeTheorems.ConjScottMap
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst9
public import DomainTheory.BridgeTheorems.conjScottMapFun
public import DomainTheory.BridgeTheorems.conjScottMapFun_le_iff
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst19
public import DomainTheory.BridgeTheorems.ext

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

namespace ConjScottMap

variable {D' E' : Type*} [PartialOrder D'] [PartialOrder E']

variable (ιD : D ≃o D') (ιE : E ≃o E')

noncomputable instance : PartialOrder (ConjScottMap ιD ιE) where
  le f g := ∀ x, conjScottMapFun ιD ιE f.scott x ≤ conjScottMapFun ιD ιE g.scott x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm f g hfg hgf := by
    refine ext ιD ιE ?_
    exact le_antisymm
      ((conjScottMapFun_le_iff ιD ιE).1 hfg)
      ((conjScottMapFun_le_iff ιD ιE).1 hgf)

end ConjScottMap

end DomainTheory.BridgeTheorems
