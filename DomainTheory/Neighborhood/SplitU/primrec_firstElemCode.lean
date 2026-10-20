/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.UComputablePresentation
public import DomainTheory.Neighborhood.SplitU.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem












theorem primrec_firstElemCode : Nat.Primrec firstElemCode :=
  Nat.Primrec.left.comp primrec_pred

end DomainTheory.Neighborhood
