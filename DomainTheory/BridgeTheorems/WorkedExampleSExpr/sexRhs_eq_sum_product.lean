/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Order.Sum.Order
import Mathlib.Order.Ideal
import DomainTheory.InformationSystems.Factoid24
import DomainTheory.InformationSystems.Factoid81
import DomainTheory.InformationSystems.Proposition54
import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
import DomainTheory.BridgeTheorems.PresentationDomains
import DomainTheory.BridgeTheorems.InfoSysConstructions
import DomainTheory.BridgeTheorems.ScottMapBridge
import DomainTheory.BridgeTheorems.SexDomainEquation
import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic


namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order






theorem sexRhs_eq_sum_product :
    SexRhs = sumSystem lowerBoundSystem (productSystem SexSys SexSys) :=
  treeRhs_eq_sum_product lowerBoundSystem

end DomainTheory.BridgeTheorems
