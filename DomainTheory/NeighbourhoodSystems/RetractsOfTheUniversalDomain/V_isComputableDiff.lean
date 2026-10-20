/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V_diff_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_Vdiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff_spec

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`V` has a computable `\`**, the missing prerequisite for Exercise 8.12(f). -/
def V_isComputableDiff : IsComputableDiff VComputablePresentation where
  diffIdx := Vdiff
  diffIdx_primrec := primrec_Vdiff
  diffIdx_spec := Vdiff_spec
  diff_computable := V_diff_computable

end DomainTheory.NeighbourhoodSystems
