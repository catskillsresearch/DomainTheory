/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.condC_map_cont


namespace DomainTheory.DataTypesAsLattices

































theorem condC_beta (x : Pomega) :
    funOf condC x = graph (fun y => graph (fun z => condSet z x y)) :=
  beta condC_map_cont x

end DomainTheory.DataTypesAsLattices
