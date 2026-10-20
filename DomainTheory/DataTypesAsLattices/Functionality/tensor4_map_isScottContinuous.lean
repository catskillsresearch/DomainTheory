/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_comp_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem tensor4_map_isScottContinuous (a b c d : Pomega) :
    IsScottContinuous (fun u =>
      seq4 (funOf a (funOf u (ofNat 0)))
        (funOf b (funOf u (ofNat 1)))
        (funOf c (funOf u (ofNat 2)))
        (funOf d (funOf u (ofNat 3)))) :=
  seq4_comp_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous a) (funOf_isScottContinuous_left (ofNat 0)))
    (theorem_1_3 (funOf_isScottContinuous b) (funOf_isScottContinuous_left (ofNat 1)))
    (theorem_1_3 (funOf_isScottContinuous c) (funOf_isScottContinuous_left (ofNat 2)))
    (theorem_1_3 (funOf_isScottContinuous d) (funOf_isScottContinuous_left (ofNat 3)))

end DomainTheory.DataTypesAsLattices
