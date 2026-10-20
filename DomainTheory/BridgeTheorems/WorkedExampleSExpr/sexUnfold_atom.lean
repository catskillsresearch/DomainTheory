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






/-- Unfolding tokens into the sum-of-product carrier (Factoid 8.1). -/
theorem sexUnfold_atom (n : ℕ) :
    treeUnfold lowerBoundSystem (.atom n) = SumToken.left n :=
  treeUnfold_atom lowerBoundSystem n

end DomainTheory.BridgeTheorems
