module

public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.RE

import DomainTheory.DataTypesAsLattices.Enumeration.bar_generated
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_17
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_16
import DomainTheory.DataTypesAsLattices.Enumeration.generatedSemigroup_mem_RE_FUN
import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_1

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace theorem_3_7

theorem equations (u v x : Pomega) :
    funOf Lcomb (funOf (funOf barComb u) (funOf Rcomb x)) = funOf u x ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x :=
  ⟨eq_3_16.bar u x, (eq_3_17.projections u v x).2.1,
    (eq_3_17.projections u v x).2.2⟩

theorem generation {u : Pomega}
    (huRE : u ∈ RE) (huFUN : u ∈ FUN) : GeneratedSemigroup u := by
  have hbar : GeneratedSemigroup (funOf barComb u) :=
    bar_generated ((theorem_3_1 (u := u)).mp huRE)
  have hgen : GeneratedSemigroup
      (enumComp Lcomb (enumComp (funOf barComb u) Rcomb)) :=
    .comp .L (.comp hbar .R)
  rw [eq_3_16.operator] at hgen
  simpa [FUN] using huFUN ▸ hgen

end theorem_3_7

theorem theorem_3_7 {u : Pomega} :
    u ∈ RE ∩ FUN ↔ GeneratedSemigroup u :=
  ⟨fun h => theorem_3_7.generation h.1 h.2, generatedSemigroup_mem_RE_FUN⟩

end DomainTheory.DataTypesAsLattices
