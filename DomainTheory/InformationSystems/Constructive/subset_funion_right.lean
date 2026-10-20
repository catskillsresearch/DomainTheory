/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Finset.Basic
import DomainTheory.InformationSystems.Constructive.Basic


namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]







theorem subset_funion_right (u v : Finset α) : v ⊆ u ∪' v := fun _ hx => mem_funion.2 (Or.inr hx)

end DomainTheory.InformationSystems.Constructive
