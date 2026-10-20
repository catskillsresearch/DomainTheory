/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise516ThueMorse
public import DomainTheory.Neighborhood.Exercise516Overlap.Basic
public import DomainTheory.Neighborhood.Exercise516Overlap.no_cube
public import DomainTheory.Neighborhood.Exercise516Overlap.tmList_getElemu3f
public import DomainTheory.Neighborhood.Exercise516Overlap.append_three_period

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood






open Example44 ExampleB NeighborhoodSystem

/-- **Exercise 5.16 (Scott 1981, PRG-19) — `t` is cube-free.** Scott's literal statement: `t` is not
of the form `u·a·a·a·v` for any finite prefix `u` and nonempty finite block `a`. (`v` is whatever
follows; we phrase "`u·a·a·a` is a prefix of `t`" as `(u·a·a·a)⊥ ⊑ t`.) -/
theorem tElt_cube_free (u a : Str) (ha : a ≠ []) :
    ¬ strBot (u ++ a ++ a ++ a) ≤ tElt := by
  intro hle
  -- `u·a·a·a` is a prefix of `t`, hence equals the Thue–Morse prefix of its length.
  have hmem : tElt.mem (cone (u ++ a ++ a ++ a)) :=
    hle _ (strBot_mem_cone.mpr List.prefix_rfl)
  have heq : u ++ a ++ a ++ a = tmList (u ++ a ++ a ++ a).length :=
    (tElt_mem_cone_iff _).mp hmem
  -- Read off a cube in `tm` at offset `|u|`, period `|a|`.
  set N := (u ++ a ++ a ++ a).length with hN
  have hlen : N = u.length + 3 * a.length := by simp only [hN, List.length_append]; omega
  have hp : 1 ≤ a.length := by
    cases a with
    | nil => exact (ha rfl).elim
    | cons _ _ => simp
  refine no_cube u.length a.length hp (fun k hk => ?_)
  -- Both `tm (|u|+k)` and `tm (|u|+|a|+k)` read the same bit of `u·a·a·a`.
  have hk3 : u.length + k < N := by omega
  have hk3' : u.length + a.length + k < N := by omega
  have e1 : (tmList N)[u.length + k]? = some (tm (u.length + k)) := tmList_getElem? hk3
  have e2 : (tmList N)[u.length + a.length + k]? = some (tm (u.length + a.length + k)) :=
    tmList_getElem? hk3'
  -- Rewrite the prefix as `u ++ (a ++ (a ++ a))` and strip `u`.
  have hassoc : u ++ a ++ a ++ a = u ++ (a ++ (a ++ a)) := by
    simp [List.append_assoc]
  rw [← heq, hassoc] at e1 e2
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + k),
    show u.length + k - u.length = k by omega] at e1
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + a.length + k),
    show u.length + a.length + k - u.length = k + a.length by omega] at e2
  -- Period: `(a++(a++a))[k]? = (a++(a++a))[k+|a|]?`.
  have hper := append_three_period a k (by omega)
  have : some (tm (u.length + k)) = some (tm (u.length + a.length + k)) := by
    rw [← e1, hper, e2]
  exact Option.some.inj this

end DomainTheory.Neighborhood.Exercise516
